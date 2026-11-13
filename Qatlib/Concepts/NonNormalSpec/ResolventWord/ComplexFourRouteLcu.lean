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

/-!
# Four-route complex polynomial block encodings

This module decomposes a complex polynomial into its real and imaginary, even and odd routes and
combines their quantum signal processing words by a four-route linear combination. The
polynomial transformation and linear-combination settings are described in
[GilyenSuLowWiebe2019] and [ChildsWiebe2012].

Given phase tables realizing the four routes and a same-frame projected unitary encoding of a
Hermitian matrix, `Native.word` compresses to the polynomial evaluated at that matrix.
Compilation uses five Boolean flags, preserves the summed phase-length query count, and supplies
explicit fixed-gate counts and additive hardware and numerical error bounds.

## Main statements

* `four_reconstruct`: The four scaled real parity routes reconstruct the complex polynomial.
* `Native.word_block`: The compiled single-control word compresses to `aeval A P`.
* `ComplexFourRouteLcu.frontier1`: Unitarity, compression error, query and gate counts, and
  register size.
* `ComplexFourRouteLcu.numerical_block_encoding`: A normalized approximate block encoding with
  combined oracle and known-gate errors.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

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

/-- The real polynomial obtained by taking the real part of each coefficient of `P`. -/
def realPolynomial (P : Polynomial ℂ) : Polynomial ℝ :=
  ⟨⟨P.toFinsupp.coeff.mapRange Complex.re rfl⟩⟩

/-- The real polynomial obtained by taking the imaginary part of each coefficient of `P`. -/
def imagPolynomial (P : Polynomial ℂ) : Polynomial ℝ :=
  ⟨⟨P.toFinsupp.coeff.mapRange Complex.im rfl⟩⟩

/-- The coefficient of `realPolynomial P` is the real part of the corresponding coefficient of
`P`. -/
@[simp] theorem real_coeff (P : Polynomial ℂ) (n : ℕ) :
    (realPolynomial P).coeff n = (P.coeff n).re := rfl

/-- The coefficient of `imagPolynomial P` is the imaginary part of the corresponding coefficient
of `P`. -/
@[simp] theorem imag_coeff (P : Polynomial ℂ) (n : ℕ) :
    (imagPolynomial P).coeff n = (P.coeff n).im := rfl

/-- A complex polynomial is the sum of its real coefficient polynomial and `I` times its
imaginary coefficient polynomial, both mapped to ℂ. -/
theorem complex_reconstruct (P : Polynomial ℂ) :
    P = (realPolynomial P).map Complex.ofRealHom +
      C Complex.I * (imagPolynomial P).map Complex.ofRealHom := by
  ext n
  simp only [coeff_add,coeff_C_mul,coeff_map,real_coeff,imag_coeff]
  simpa only [mul_comm] using! (Complex.re_add_im (P.coeff n)).symm

/-- At a real input, the real and imaginary coefficient polynomials evaluate to the real and
imaginary parts of the complex polynomial's value. -/
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

/-- The even part `(p(X) + p(-X)) / 2` of a real polynomial. -/
def evenPart (p : Polynomial ℝ) : Polynomial ℝ := C (1/2) * (p + p.comp (-X))
/-- The odd part `(p(X) - p(-X)) / 2` of a real polynomial. -/
def oddPart (p : Polynomial ℝ) : Polynomial ℝ := C (1/2) * (p - p.comp (-X))

/-- The even and odd parts of a real polynomial sum to the original polynomial. -/
theorem parity_reconstruct (p : Polynomial ℝ) : evenPart p + oddPart p = p := by
  ext n
  simp only [evenPart,oddPart,coeff_add,coeff_C_mul,coeff_sub]
  ring

/-- The even part of a real polynomial has real parity zero. -/
theorem evenPart_parity (p : Polynomial ℝ) : HasRealParity 0 (evenPart p) := by
  simp only [HasRealParity,evenPart,mul_comp,C_comp,add_comp,comp_assoc,neg_comp,X_comp,
    neg_neg,comp_X,pow_zero,C_1,one_mul]
  ring

/-- The odd part of a real polynomial has real parity one. -/
theorem oddPart_parity (p : Polynomial ℝ) : HasRealParity 1 (oddPart p) := by
  simp only [HasRealParity,oddPart,mul_comp,C_comp,sub_comp,comp_assoc,neg_comp,X_comp,
    neg_neg,comp_X,pow_one,C_neg,C_1,neg_one_mul]
  ring

/-- The even part evaluates to the average of `p.eval x` and `p.eval (-x)`. -/
theorem even_eval (p : Polynomial ℝ) (x : ℝ) :
    (evenPart p).eval x = (p.eval x+p.eval (-x))/2 := by
  simp [evenPart]
  ring

/-- The odd part evaluates to half the difference of `p.eval x` and `p.eval (-x)`. -/
theorem odd_eval (p : Polynomial ℝ) (x : ℝ) :
    (oddPart p).eval x = (p.eval x-p.eval (-x))/2 := by
  simp [oddPart]
  ring

/-- Selects the real or imaginary coefficient polynomial and then its even or odd part according
to the two Boolean flags. -/
def component (P : Polynomial ℂ) (imag odd : Bool) : Polynomial ℝ :=
  let p := if imag then imagPolynomial P else realPolynomial P
  if odd then oddPart p else evenPart p

/-- The selected real parity component of `P`, scaled by four for the four-route construction. -/
def routePolynomial (P : Polynomial ℂ) (imag odd : Bool) : Polynomial ℝ :=
  C 4 * component P imag odd

/-- The route phase, equal to `I` for an imaginary route and one for a real route. -/
def routePhase (imag : Bool) : ℂ := if imag then Complex.I else 1

/-- Averaging the four route polynomials with their real or imaginary phases reconstructs `P`
exactly. -/
theorem four_reconstruct (P : Polynomial ℂ) :
    (1/4 : ℂ) • (∑ b : Bool, ∑ c : Bool,
      C (routePhase b) * (routePolynomial P b c).map Complex.ofRealHom) = P := by
  ext n
  simp [routePolynomial,component,evenPart,oddPart,routePhase]
  conv_rhs => rw [← Complex.re_add_im (P.coeff n)]
  ring

/-- If `P` has norm at most `1/4` on `[-1,1]`, every real parity component has absolute value at
most `1/4` on that interval. -/
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

/-- If `P` has norm at most `1/4` on `[-1,1]`, each scaled route polynomial has absolute value
at most one on that interval. -/
theorem route_bound (P : Polynomial ℂ)
    (hP : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖P.eval (x : ℂ)‖ ≤ 1/4)
    (b c : Bool) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(routePolynomial P b c).eval x| ≤ 1 := by
  have hb := component_bound P hP b c x hx
  simp only [routePolynomial,eval_mul,eval_C,abs_mul]
  rw [abs_of_pos (by norm_num : (0 : ℝ)<4)]
  linarith

/-- The selected component has odd parity when its second flag is `true` and even parity
otherwise. -/
theorem component_parity (P : Polynomial ℂ) (b c : Bool) :
    HasRealParity (if c then 1 else 0) (component P b c) := by
  cases c
  · simpa only [component,Bool.false_eq_true,if_false] using!
      evenPart_parity (if b then imagPolynomial P else realPolynomial P)
  · simpa only [component,if_true] using!
      oddPart_parity (if b then imagPolynomial P else realPolynomial P)

/-- The scaled route polynomial has odd parity when its second flag is `true` and even parity
otherwise. -/
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

/-- For Hermitian `A` and a real polynomial of odd parity, its odd singular transform equals the
polynomial evaluated at `A` after mapping coefficients to ℂ. -/
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

/-- For Hermitian `A` and a real polynomial of even parity, its right singular transform equals
the polynomial evaluated at `A` after mapping coefficients to ℂ. -/
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

/-- For a same-frame projected encoding of Hermitian `A`, a source phase word with the stated
real polynomial response gives a same-frame projected encoding of that polynomial evaluated
at `A`. -/
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

/-- Taking the adjoint of `cppDataOracle U` is equivalent to replacing `U` by its adjoint. -/
theorem cppDataOracle_adjoint {J : Type} [DecidableEq J] (U : Matrix H H ℂ) :
    (cppDataOracle (J:=J) U)ᴴ = cppDataOracle (J:=J) Uᴴ := by
  simp [cppDataOracle, parallelOracle_adjoint, Matrix.conjTranspose_kronecker]

/-- Evaluating the compiled adjoint word for CPP steps with `cppDataOracle U` gives `cppEvaluate
U P Q ss`. -/
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

/-- The compiled CPP word has the query count from `cppCounts` and fixed-gate count equal to the
sum of its three gate-count components. -/
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

/-- Evaluating the source CPP adjoint word with the CPP data oracle gives `sourceRealWord`. -/
theorem sourceWord_eval (U P Q : Matrix H H ℂ) (Φ : List ℝ) :
    evaluate (cppDataOracle (J:=Bool) U) (sourceCppAdjointWord P Q Φ)
      = sourceRealWord U P Q Φ := by
  unfold sourceCppAdjointWord sourceRealWord
  split_ifs
  · exact cppWord_eval U P Q _
  · rw [evaluate_swapQueries, cppDataOracle_adjoint, cppWord_eval, ← cppEvaluate_swapData]

omit [Fintype H] in

/-- A source CPP adjoint word with phase list `Φ` uses `Φ.length` queries and `3 * Φ.length`
fixed gates. -/
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

/-- Compiles four adjoint words into a word selected by two nested Boolean controls. -/
noncomputable def fourWord (cs : Bool → Bool → List (AdjointStep H)) :
    List (AdjointStep (Bool × (Bool × H))) :=
  compileSelected (compileSelected (cs true true) (cs true false))
    (compileSelected (cs false true) (cs false false))

/-- Evaluating `fourWord` with the twice-controlled oracle yields the nested selection of the
four branch evaluations. -/
theorem fourWord_eval (U : Matrix H H ℂ) (cs : Bool → Bool → List (AdjointStep H)) :
    evaluate (controlOracle (controlOracle U)) (fourWord cs) =
      select (fun b : Bool => select (fun c : Bool => evaluate U (cs b c))) := by
  simp only [fourWord, evaluate_compileSelected]
  congr 1
  funext b
  cases b <;> simp <;> congr 1 <;> funext c <;> cases c <;> simp

omit [Fintype H] in

/-- The four-route word uses the sum of branch query counts and the sum of branch fixed-gate
counts plus six. -/
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

/-- The reassociation equivalence from `Bool × (Bool × H)` to `(Bool × Bool) × H`. -/
def assoc : Bool × (Bool × H) ≃ (Bool × Bool) × H := (Equiv.prodAssoc Bool Bool H).symm

omit [Fintype H] [DecidableEq H] in

/-- Nested Boolean selection equals selection by a pair of Boolean labels after reassociating
the indices. -/
theorem nested_select (V : Bool × Bool → Matrix H H ℂ) :
    select (fun b : Bool => select (fun c : Bool => V (b,c))) =
      (select V).submatrix (assoc (H:=H)) assoc := by
  ext ⟨b,c,i⟩ ⟨b',c',j⟩
  by_cases hb : b=b' <;> by_cases hc : c=c' <;>
    simp [select, assoc, Matrix.submatrix_apply, hb, hc, Prod.ext_iff]

/-- Compressing the four-route word between amplitude-preparation frames gives the weighted sum
of branch evaluations, with weights `star (a j) * b j`. -/
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

/-- The uniform left route amplitudes, each equal to `1/2`. -/
noncomputable def leftAmp : Bool × Bool → ℂ := fun _ => 1/2

/-- The right route amplitudes, equal to `I/2` on imaginary routes and `1/2` on real routes. -/
noncomputable def rightAmp : Bool × Bool → ℂ := fun j => if j.1 then Complex.I/2 else 1/2

/-- The four left route amplitudes have squared moduli summing to one. -/
theorem leftAmp_normalized : ∑ j : Bool × Bool, star (leftAmp j) * leftAmp j = 1 := by
  norm_num [leftAmp, Fintype.sum_prod_type, Fintype.sum_bool]

/-- The four right route amplitudes have squared moduli summing to one. -/
theorem rightAmp_normalized : ∑ j : Bool × Bool, star (rightAmp j) * rightAmp j = 1 := by
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ _
  norm_num [rightAmp, Fintype.sum_prod_type, Fintype.sum_bool, h2]
  ring_nf
  norm_num [Complex.I_sq]

/-- For a unitary oracle and four well-formed branch words, evaluation of the actual four-route
word is unitary. -/
theorem actual_four_word_unitary (O : Matrix H H ℂ)
    (hO : O ∈ unitaryGroup H ℂ) (cs : Bool → Bool → List (AdjointStep H))
    (hcs : ∀ b c, WellFormedAdjointCircuit (cs b c)) :
    evaluate (controlOracle (controlOracle O)) (fourWord cs) ∈ unitaryGroup (Bool × (Bool × H)) ℂ := by
  apply WellFormedAdjointCircuit.evaluate_unitary
  · exact compileSelected_wellFormed
      (compileSelected_wellFormed (hcs true true) (hcs true false))
      (compileSelected_wellFormed (hcs false true) (hcs false false))
  · exact controlOracle_unitary (controlOracle_unitary hO)

/-- Compiling CPP steps with orthogonal projectors produces a well-formed adjoint circuit. -/
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

/-- The source CPP adjoint word is well formed when its two matrix parameters are orthogonal
projectors. -/
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

/-- The Hadamard gate on the outer route flag, with identity action on the other registers. -/
noncomputable def hOuter : Matrix (Bool × (Bool × K)) (Bool × (Bool × K)) ℂ := TensorGate Hadamard 1
/-- The Hadamard gate on the inner route flag, with identity action on the outer flag and data
register. -/
noncomputable def hInner : Matrix (Bool × (Bool × K)) (Bool × (Bool × K)) ℂ :=
  TensorGate 1 (TensorGate Hadamard 1)
/-- The two-route-flag preparation applying a Hadamard to each flag and the identity to the data
register. -/
noncomputable def prep : Matrix (Bool × (Bool × K)) (Bool × (Bool × K)) ℂ :=
  TensorGate Hadamard (TensorGate Hadamard 1)
/-- The phase gate multiplying the outer `true` route branch by `I`. -/
noncomputable def imagPhase : Matrix (Bool × (Bool × K)) (Bool × (Bool × K)) ℂ :=
  TensorGate (Matrix.diagonal (fun b : Bool => if b then Complex.I else 1)) 1
/-- The frame obtained by adding two clean Boolean route flags to `F`. -/
noncomputable def routeFrame (F : Matrix K I ℂ) : Matrix (Bool × (Bool × K)) I ℂ :=
  cppCleanFrame (cppCleanFrame F)

omit [Fintype I] [DecidableEq I] in

/-- Applying the inner and outer route Hadamards in the stated product gives `prep`. -/
theorem hOuter_hInner : hOuter (K:=K) * hInner = prep := by
  simp [hOuter, hInner, prep, tensorGate_mul]
omit [Fintype I] [DecidableEq I] in

/-- The reverse order of the two route Hadamards also gives `prep`. -/
theorem hInner_hOuter : hInner (K:=K) * hOuter = prep := by
  simp [hOuter, hInner, prep, tensorGate_mul]
omit [Fintype I] [DecidableEq I] in

/-- The two-flag preparation matrix is self-adjoint. -/
theorem prep_adjoint : (prep (K:=K))ᴴ = prep := by
  simp [prep, tensorGate_conjTranspose, hadamard_conjTranspose]

omit [Fintype I] [DecidableEq I] in

/-- Applying `prep` to the clean route frame yields the uniform route-amplitude lift of `F`. -/
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

/-- Applying the imaginary-route phase gate to the left-amplitude lift of `F` yields the
right-amplitude lift. -/
theorem phase_liftAmp (F : Matrix K I ℂ) :
    imagPhase * (((prepareLift leftAmp).submatrix (assoc (H:=K)) id) * F)
      = ((prepareLift rightAmp).submatrix (assoc (H:=K)) id) * F := by
  ext ⟨b,c,k⟩ i
  cases b <;> simp [imagPhase, TensorGate, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.diagonal_apply, Matrix.one_apply, prepareLift,
    Matrix.submatrix_apply, leftAmp, rightAmp, assoc, div_eq_mul_inv, mul_assoc]

/-- The four-route word with explicit route preparation, imaginary phase, and unpreparation
gates. -/
noncomputable def physicalWord (cs : Bool → Bool → List (AdjointStep K)) :
    List (AdjointStep (Bool × (Bool × K))) :=
  [.gate hInner, .gate hOuter] ++ fourWord cs ++ [.gate imagPhase, .gate hOuter, .gate hInner]

omit [Fintype I] [DecidableEq I] in

/-- The physical route word evaluates to `prep * fourWordEvaluation * imagPhase * prep` with the
stated twice-controlled oracle. -/
theorem physicalWord_eval (O : Matrix K K ℂ) (cs : Bool → Bool → List (AdjointStep K)) :
    evaluate (controlOracle (controlOracle O)) (physicalWord cs)
      = prep * evaluate (controlOracle (controlOracle O)) (fourWord cs) * imagPhase * prep := by
  simp only [physicalWord, evaluate_append, evaluate, instructionMatrix, Matrix.mul_one]
  rw [hInner_hOuter]
  have h := hOuter_hInner (K:=K)
  simp only [Matrix.mul_assoc] at h ⊢
  rw [h]

omit [Fintype K] [Fintype I] [DecidableEq I] in

/-- The physical route word uses the sum of branch query counts and the sum of branch fixed-gate
counts plus eleven. -/
theorem physicalWord_counts (cs : Bool → Bool → List (AdjointStep K)) :
    adjointQueryCount (physicalWord cs) = ∑ b : Bool, ∑ c : Bool, adjointQueryCount (cs b c) ∧
    adjointGateCount (physicalWord cs) = (∑ b : Bool, ∑ c : Bool, adjointGateCount (cs b c)) + 11 := by
  have h := fourWord_counts cs
  simp only [physicalWord, adjointQueryCount_append, adjointGateCount_append,
    adjointQueryCount, adjointGateCount]
  omega

omit [Fintype I] [DecidableEq I] in

/-- Compression of the physical route word to the clean route frame is the weighted sum of the
compressed branch evaluations. -/
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

/-- Compression of the physical route word is one quarter of the sum of compressed branches,
weighted by one on real routes and `I` on imaginary routes. -/
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

/-- For source CPP branches, the physical route word uses the total phase-list length in queries
and three times that length plus eleven fixed gates. -/
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

/-- The source register space with two Boolean flags preceding `H`. -/
abbrev SourceSpace (H : Type) := Bool × (Bool × H)
/-- The canonical register space with two route flags preceding the two-flag source space. -/
abbrev CanonSpace (H : Type) := Bool × (Bool × SourceSpace H)

/-- The Hadamard on the real-average flag of the source space. -/
noncomputable def realavgGate : Matrix (SourceSpace H) (SourceSpace H) ℂ := TensorGate Hadamard 1
/-- The source frame obtained from `F` by adding two Boolean flags initialized to `false`. -/
noncomputable def allZeroSource (F : Matrix H I ℂ) : Matrix (SourceSpace H) I ℂ :=
  cppCleanFrame (cppCleanFrame F)

/-- The unit complex phase `(1-I) / sqrt 2` used to align real-average amplitudes. -/
noncomputable def avgPhase : ℂ := (Real.sqrt 2 : ℂ)⁻¹ * (1-Complex.I)

/-- Multiplying either real-part amplitude by `avgPhase` gives `1 / sqrt 2`. -/
theorem avgPhase_amplitude (b : Bool) :
    avgPhase * realPartAmplitude b = (Real.sqrt 2 : ℂ)⁻¹ := by
  unfold avgPhase realPartAmplitude
  ring_nf
  norm_num [Complex.I_sq]
  ring

/-- The complex phase `avgPhase` has squared modulus one. -/
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

/-- Applying the real-average Hadamard to the all-zero source frame gives `sourceAverageClean F`
up to the common phase `avgPhase`. -/
theorem realavg_prepare (F : Matrix H I ℂ) :
    realavgGate * allZeroSource F = avgPhase • sourceAverageClean F := by
  ext ⟨b,c,h⟩ i
  have hc := avgPhase_amplitude b
  cases c <;> simp [realavgGate, allZeroSource, sourceAverageClean, averageFrame,
    cppCleanFrame, TensorGate, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.one_apply, prepareLift, Matrix.smul_apply, hadamard_apply_false, ← mul_assoc, hc]

/-- The source real-average gate lifted through the two route flags as spectator registers. -/
noncomputable def spectatorAvgGate : Matrix (CanonSpace H) (CanonSpace H) ℂ :=
  TensorGate 1 (TensorGate 1 (realavgGate (H:=H)))
/-- The canonical frame formed by adding two clean source flags and two clean route flags to
`F`. -/
noncomputable def canonicalFrame (F : Matrix H I ℂ) : Matrix (CanonSpace H) I ℂ :=
  routeFrame (allZeroSource F)

omit [DecidableEq H] in

/-- A source-space gate acting below the two route flags sends `routeFrame F` to `routeFrame
(V*F)`. -/
theorem spectator_route_action (V : Matrix (SourceSpace H) (SourceSpace H) ℂ)
    (F : Matrix (SourceSpace H) I ℂ) :
    TensorGate 1 (TensorGate 1 V) * routeFrame F = routeFrame (V*F) := by
  ext ⟨b,c,h⟩ i
  cases b <;> cases c <;> simp [routeFrame, cppCleanFrame, TensorGate,
    Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply]

omit [Fintype H] [DecidableEq H] in

/-- Adding clean route flags commutes with scalar multiplication of the frame. -/
theorem routeFrame_smul (z : ℂ) (F : Matrix (SourceSpace H) I ℂ) :
    routeFrame (z • F) = z • routeFrame F := by
  ext ⟨b,c,h⟩ i
  cases b <;> cases c <;> simp [routeFrame, cppCleanFrame, Matrix.smul_apply]

/-- Applying the spectator real-average gate to the canonical frame yields the route frame of
`sourceAverageClean F`, up to `avgPhase`. -/
theorem canonical_prepare (F : Matrix H I ℂ) :
    spectatorAvgGate * canonicalFrame F = avgPhase • routeFrame (sourceAverageClean F) := by
  rw [spectatorAvgGate, canonicalFrame, spectator_route_action, realavg_prepare, routeFrame_smul]

omit [DecidableEq H] in

/-- Multiplying both compression frames by the same unit complex phase leaves the compressed
matrix unchanged. -/
theorem compress_phase_frame (z : ℂ) (F : Matrix (CanonSpace H) I ℂ)
    (W : Matrix (CanonSpace H) (CanonSpace H) ℂ) (hz : star z*z=1) :
    compress (z • F) W (z • F) = compress F W F := by
  have hz' : z * star z = 1 := (mul_comm z (star z)).trans hz
  simp only [compress, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  exact (congrArg (fun c : ℂ => c • (Fᴴ * W * F)) hz').trans (one_smul ℂ _)

omit I in

/-- The spectator real-average gate is self-adjoint. -/
theorem spectatorAvgGate_adjoint : (spectatorAvgGate (H:=H))ᴴ = spectatorAvgGate := by
  simp [spectatorAvgGate, realavgGate, tensorGate_conjTranspose, hadamard_conjTranspose]

/-- Wraps the physical four-route word with the spectator real-average gate on both sides. -/
noncomputable def canonicalWord (cs : Bool → Bool → List (AdjointStep (SourceSpace H))) :
    List (AdjointStep (CanonSpace H)) :=
  [.gate spectatorAvgGate] ++ physicalWord cs ++ [.gate spectatorAvgGate]

/-- Compression of the canonical word to the canonical frame equals compression of the physical
word to the route frame of `sourceAverageClean F`. -/
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

/-- The canonical source word uses the total phase-list length in queries and three times that
length plus thirteen fixed gates. -/
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

/-- The canonical register space has cardinality `2^4 * card H`, accounting for its four Boolean
flags. -/
theorem canonical_four_flags : Fintype.card (CanonSpace H) = 2^4 * Fintype.card H := by
  simp [CanonSpace, SourceSpace, Fintype.card_prod]
  ring

omit [Fintype H] [DecidableEq H] in

/-- The canonical frame equals `F` when all four flags are `false` and vanishes whenever any
flag is `true`. -/
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

/-- Four real phase lists whose source responses realize the four route polynomials, with parity
matching each list's length. -/
structure PhaseTables (P : Polynomial ℂ) where
  phases : Bool → Bool → List ℝ
  parity : ∀ b c, HasRealParity (phases b c).length (routePolynomial P b c)
  response : ∀ b c (x : ℝ), ((sourcePhaseResponse (phases b c)).eval (x : ℂ)).re =
    (routePolynomial P b c).eval x

variable {I H : Type} [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]

/-- The canonical ideal four-route word built from the phase tables and the range projector of
`F`. -/
def idealWord (F : Matrix H I ℂ) {P : Polynomial ℂ} (tables : PhaseTables P) :
    List (AdjointStep (CanonSpace H)) :=
  canonicalWord (fun b c => sourceCppAdjointWord (rangeProjector F) (rangeProjector F)
    (tables.phases b c))

/-- Given a same-frame projected unitary encoding of Hermitian `A` and phase tables for `P`, the
ideal four-route word compresses to `aeval A P`. -/
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

/-- The ideal word uses the total phase-list length in queries and three times that length plus
thirteen fixed gates. -/
theorem idealWord_counts (F : Matrix H I ℂ) {P : Polynomial ℂ} (tables : PhaseTables P) :
    adjointQueryCount (idealWord F tables) = ∑ b : Bool, ∑ c : Bool, (tables.phases b c).length ∧
    adjointGateCount (idealWord F tables) =
      3 * (∑ b : Bool, ∑ c : Bool, (tables.phases b c).length) + 13 :=
  canonical_source_counts _ _ _

end Qatlib.Concepts.NonNormalSpec.ResolventWord.ComplexFourRouteLcu

open Qatlib.Concepts.NonNormalSpec.ResolventWord.ComplexFourRouteLcu

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord.SingleControl
variable {J H : Type} [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]
/-- The base register space consisting of a route label `J` and data register `H`. -/
abbrev Base (J H : Type) := J × H
/-- The working register space obtained by adding a Boolean flag between the route label and
data register. -/
abbrev Work (J H : Type) := J × (Bool × H)

/-- Matrix multiplication with an explicitly specified finite summation index type. -/
abbrev multiply {M N K : Type} [Fintype N] (A : Matrix M N ℂ) (B : Matrix N K ℂ) : Matrix M K ℂ :=
  @HMul.hMul (Matrix M N ℂ) (Matrix N K ℂ) (Matrix M K ℂ)
    Matrix.instHMulOfFintypeOfMulOfAddCommMonoid A B

/-- The explicitly specified matrix multiplication `multiply` is associative. -/
private theorem mm_assoc {L M N K : Type} [Fintype M] [Fintype N]
    (A : Matrix L M ℂ) (B : Matrix M N ℂ) (C : Matrix N K ℂ) :
    multiply (multiply A B) C = multiply A (multiply B C) := Matrix.mul_assoc A B C

/-- Inserts the Boolean work flag `w` into a base register value. -/
def insert (w : Bool) (x : Base J H) : Work J H := (x.1,(w,x.2))
/-- The matrix embedding the base space into the work space with its Boolean flag initialized to
`false`. -/
def clean : Matrix (Work J H) (Base J H) ℂ :=
  (1 : Matrix (Work J H) (Work J H) ℂ).submatrix id (insert false)

local notation "E" => (clean (J:=J) (H:=H))

/-- The clean work-space embedding is isometric: its adjoint multiplied by itself is the
identity. -/
theorem clean_isometry : multiply Eᴴ E = 1 := by
  apply Matrix.submatrix_one_id_right_isometry
  intro x y he
  have hh := congrArg (fun z : Work J H => (z.1,z.2.2)) he
  exact hh

/-- Right multiplication by the clean embedding selects the columns whose work flag is `false`. -/
theorem mul_clean (M : Matrix (Work J H) (Work J H) ℂ) (a : Work J H) (b : Base J H) :
    (multiply M E) a b = M a (insert false b) := by
  simp [multiply,Matrix.mul_apply,clean,Matrix.submatrix_apply,Matrix.one_apply]

/-- Left multiplication by the clean embedding embeds a base-space matrix in the `false`
work-flag rows and gives zero in the remaining rows. -/
theorem clean_mul (M : Matrix (Base J H) (Base J H) ℂ) (a : Work J H) (b : Base J H) :
    (multiply E M) a b = if a.2.1=false then M (a.1,a.2.2) b else 0 := by
  rcases a with ⟨j,w,h⟩
  cases w <;> simp [multiply,Matrix.mul_apply,clean,insert,Matrix.submatrix_apply,Matrix.one_apply,
    Fintype.sum_prod_type,ite_and]

/-- The equivalence moving the Boolean work flag to the front of the route-label and data
registers. -/
def workEquiv : Work J H ≃ Bool × Base J H where
  toFun z := (z.2.1,(z.1,z.2.2))
  invFun z := (z.2.1,(z.1,z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Lifts a fixed base-space gate to act identically in both work-flag sectors, using
`workEquiv` to restore register order. -/
def liftFixed (G : Matrix (Base J H) (Base J H) ℂ) : Matrix (Work J H) (Work J H) ℂ :=
  relabelGate (workEquiv (J:=J) (H:=H)).symm (parallelOracle (J:=Bool) G)

/-- The lifted fixed gate is unitary whenever the original base-space gate is unitary. -/
theorem liftFixed_unitary {G : Matrix (Base J H) (Base J H) ℂ}
    (hG : G ∈ Matrix.unitaryGroup (Base J H) ℂ) : liftFixed G ∈ Matrix.unitaryGroup (Work J H) ℂ :=
  (relabelGate_mem_unitaryGroup _ _).mpr (parallelOracle_unitary hG)

/-- The lifted fixed gate intertwines with the clean embedding and the original base-space gate. -/
theorem liftFixed_clean (G : Matrix (Base J H) (Base J H) ℂ) : multiply (liftFixed G) E = multiply E G := by
  ext a b
  rw [mul_clean,clean_mul]
  simp [liftFixed,relabelGate,Matrix.reindex_apply,workEquiv,parallelOracle,select,insert]

/-- Flips the work flag exactly when the route predicate `p` is true. -/
def flipWork (p : J → Bool) (a : Work J H) : Work J H := (a.1,(a.2.1 ^^ p a.1,a.2.2))
omit [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H] in

/-- Flipping the work flag according to the same route predicate twice returns the original
register value. -/
theorem flipWork_involutive (p : J → Bool) : Function.Involutive (flipWork (H:=H) p) := by
  intro a
  simp [flipWork]

/-- The permutation matrix implementing the route-dependent work-flag flip. -/
def toggle (p : J → Bool) : Matrix (Work J H) (Work J H) ℂ := permMatrix (flipWork p)

/-- The route-dependent work-flag toggle is unitary. -/
theorem toggle_unitary (p : J → Bool) : toggle (H:=H) p ∈ Matrix.unitaryGroup (Work J H) ℂ :=
  permMatrix_unitary (flipWork_involutive p)

/-- Left multiplication by the toggle permutes a matrix's rows by `flipWork p`. -/
theorem toggle_mul (p : J → Bool) (M : Matrix (Work J H) (Work J H) ℂ) (a b : Work J H) :
    (multiply (toggle (H:=H) p) M) a b = M (flipWork p a) b := by
  change ApplyGate (permMatrix (flipWork p)) (fun x => M x b) a = _
  exact applyGate_permMatrix (flipWork_involutive p) _ _

/-- Right multiplication by the toggle permutes a matrix's columns by `flipWork p`. -/
theorem mul_toggle (p : J → Bool) (M : Matrix (Work J H) (Work J H) ℂ) (a b : Work J H) :
    (multiply M (toggle (H:=H) p)) a b = M a (flipWork p b) := by
  simp [multiply,Matrix.mul_apply,toggle,permMatrix]

/-- The route-diagonal matrix acting as `U` where `p j` is true and as the identity elsewhere. -/
def conditional (p : J → Bool) (U : Matrix H H ℂ) : Matrix (Base J H) (Base J H) ℂ :=
  select (fun j => if p j then U else 1)

/-- Conjugating the parallel controlled oracle by route-dependent toggles implements
`conditional p U` on the clean work subspace. -/
theorem routed_query (p : J → Bool) (U : Matrix H H ℂ) :
    multiply (multiply (multiply (toggle (H:=H) p) (parallelOracle (J:=J) (controlOracle U))) (toggle (H:=H) p)) E = multiply E (conditional p U) := by
  ext ⟨j,w,h⟩ ⟨k,l⟩
  rw [mul_clean,mul_toggle,toggle_mul,clean_mul]
  by_cases he : j=k
  · subst k
    cases w <;> cases hp : p j <;>
      simp [parallelOracle,controlOracle,conditional,select,flipWork,insert,hp,Matrix.one_apply]
  · simp [parallelOracle,controlOracle,conditional,select,flipWork,insert,he]

/-- Compiles a base adjoint step by lifting fixed gates and surrounding forward or backward
queries with work-flag toggles. -/
def compileStep (p : J → Bool) : AdjointStep (Base J H) → List (AdjointStep (Work J H))
  | .gate G => [.gate (liftFixed G)]
  | .forward => [.gate (toggle p), .forward, .gate (toggle p)]
  | .backward => [.gate (toggle p), .backward, .gate (toggle p)]
/-- Compiles a base adjoint word by concatenating the route-dependent compilation of each step. -/
def compile (p : J → Bool) (cs : List (AdjointStep (Base J H))) :
    List (AdjointStep (Work J H)) := cs.flatMap (compileStep p)

omit [Fintype J] [Fintype H] in

/-- Taking the adjoint of a conditional oracle replaces its data matrix by its adjoint. -/
theorem conditional_adjoint (p : J → Bool) (U : Matrix H H ℂ) :
    (conditional p U)ᴴ = conditional p Uᴴ := by
  rw [conditional, parallel_select_adjoint]
  congr 1
  funext j
  cases p j <;> simp

/-- Evaluation of a compiled single step intertwines the clean embedding with the original step
interpreted using `conditional p U`. -/
theorem compileStep_clean (p : J → Bool) (U : Matrix H H ℂ) (s : AdjointStep (Base J H)) :
    multiply (evaluate (parallelOracle (J:=J) (controlOracle U)) (compileStep p s)) E =
      multiply E (instructionMatrix (conditional p U) s) := by
  cases s with
  | gate G => simpa [compileStep,evaluate,instructionMatrix] using! liftFixed_clean G
  | forward => simpa [compileStep,evaluate,instructionMatrix,Matrix.mul_assoc] using! routed_query p U
  | backward =>
    simpa [compileStep,evaluate,instructionMatrix,Matrix.mul_assoc,
      parallelOracle_adjoint,controlOracle_adjoint,conditional_adjoint] using! routed_query p Uᴴ

/-- Evaluation of the compiled word intertwines the clean embedding with the original word
evaluated using `conditional p U`. -/
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

/-- Single-control compilation preserves query count and adds exactly two fixed gates per query. -/
theorem compile_counts (p : J → Bool) (cs : List (AdjointStep (Base J H))) :
    adjointQueryCount (compile p cs) = adjointQueryCount cs ∧
    adjointGateCount (compile p cs) = adjointGateCount cs + 2 * adjointQueryCount cs := by
  induction cs with
  | nil => simp [compile,adjointQueryCount,adjointGateCount]
  | cons s cs ih =>
    cases s <;> simp
        [compile,List.flatMap_cons,compileStep,adjointQueryCount,adjointGateCount] at * <;> omega

/-- Single-control compilation preserves well-formedness of adjoint circuits. -/
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

/-- The four-Boolean header storing the canonical flags separately from the data register. -/
abbrev Header := Bool × (Bool × (Bool × Bool))

/-- The equivalence packing the four canonical Boolean flags into `Header` and leaving `H` as
the data register. -/
def pack {H : Type} : CanonSpace H ≃ Header × H where
  toFun z := ((z.1,(z.2.1,(z.2.2.1,z.2.2.2.1))),z.2.2.2.2)
  invFun z := (z.1.1,(z.1.2.1,(z.1.2.2.1,(z.1.2.2.2,z.2))))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The predicate enabling a route precisely when the first two header flags are both `true`. -/
def routeEnabled (j : Header) : Bool := j.1 && j.2.1

/-- Relabels a fixed gate by an equivalence while leaving forward and backward query
instructions unchanged. -/
noncomputable def relabelAdjointStep {K L : Type} (e : K ≃ L) : AdjointStep K → AdjointStep L
  | .gate G => .gate (relabelGate e G)
  | .forward => .forward
  | .backward => .backward
/-- Relabels every instruction of an adjoint word by the register equivalence `e`. -/
noncomputable def relabelWord {K L : Type} (e : K ≃ L) (cs : List (AdjointStep K)) :
    List (AdjointStep L) := cs.map (relabelAdjointStep e)

/-- Register relabeling commutes with taking the matrix adjoint. -/
theorem relabel_adjoint {K L : Type} (e : K ≃ L) (U : Matrix K K ℂ) :
    (relabelGate e U)ᴴ = relabelGate e Uᴴ := by
  ext i j
  rfl

/-- Evaluating a relabeled word with the relabeled oracle equals relabeling the original word's
evaluation. -/
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

/-- Relabeling an adjoint word preserves both its query count and its fixed-gate count. -/
theorem relabel_counts {K L : Type} (e : K ≃ L) (cs : List (AdjointStep K)) :
    adjointQueryCount (relabelWord e cs) = adjointQueryCount cs ∧
    adjointGateCount (relabelWord e cs) = adjointGateCount cs := by
  induction cs with
  | nil => exact ⟨rfl,rfl⟩
  | cons s cs ih =>
    cases s <;> simp only [relabelWord,List.map_cons,relabelAdjointStep,
      adjointQueryCount,adjointGateCount] at * <;> omega

/-- Relabeling an adjoint word preserves well-formedness. -/
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

/-- Packing the flags turns the nested controlled CPP data oracle into the conditional oracle
with predicate `routeEnabled`. -/
theorem packed_oracle (U : Matrix H H ℂ) :
    relabelGate (pack (H:=H)) (controlOracle (controlOracle (cppDataOracle (J:=Bool) U))) =
      conditional routeEnabled U := by
  ext ⟨⟨r,s,a,c⟩,h⟩ ⟨⟨r',s',a',c'⟩,h'⟩
  cases r <;> cases s <;> cases r' <;> cases s' <;>
    simp [relabelGate,Matrix.reindex_apply,pack,conditional,routeEnabled,controlOracle,
      cppDataOracle,parallelOracle,select,Matrix.one_apply,Prod.ext_iff,
      and_left_comm,and_comm,ite_and] <;> split_ifs <;> simp_all

/-- The native four-route word obtained by packing the ideal word and compiling it with one
additional work flag and the `routeEnabled` predicate. -/
def word (F : Matrix H I ℂ) {P : Polynomial ℂ} (tables : PhaseTables P) :
    List (AdjointStep (Work Header H)) := compile routeEnabled (relabelWord pack (idealWord F tables))

/-- The native compression frame obtained by packing the canonical frame and embedding it with a
clean work flag. -/
def frame (F : Matrix H I ℂ) : Matrix (Work Header H) I ℂ :=
  multiply (clean (J:=Header) (H:=H)) ((canonicalFrame F).submatrix pack.symm id)

omit [DecidableEq I] [Fintype H] in

/-- The native word uses the total phase-list length in queries and five times that length plus
thirteen fixed gates. -/
theorem word_counts (F : Matrix H I ℂ) {P : Polynomial ℂ} (tables : PhaseTables P) :
    adjointQueryCount (word F tables) = ∑ b : Bool, ∑ c : Bool, (tables.phases b c).length ∧
    adjointGateCount (word F tables) = 5 * (∑ b : Bool, ∑ c : Bool, (tables.phases b c).length) + 13 := by
  have hc := compile_counts routeEnabled (relabelWord pack (idealWord F tables))
  have hr := relabel_counts pack (idealWord F tables)
  have hi := idealWord_counts F tables
  simp only [word]
  constructor <;> omega

omit I [DecidableEq I] [DecidableEq H] in

/-- The native working register space has cardinality `2^5 * card H`, accounting for its five
Boolean flags. -/
theorem five_flags : Fintype.card (Work Header H) = 2^5 * Fintype.card H := by
  simp [Work,Header,Fintype.card_prod]
  ring

end Qatlib.Concepts.NonNormalSpec.ResolventWord.Native

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord.SingleControl
variable {J H : Type} [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]

/-- Compression of the compiled word to the clean work subspace equals evaluation of the
original word with the conditional oracle. -/
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

/-- Packing the canonical indices preserves compression when both frames and the matrix are
relabeled consistently. -/
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

/-- Given a same-frame projected encoding of Hermitian `A` and phase tables for `P`, the native
single-control word compresses to `aeval A P`. -/
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

/-- Combining four well-formed branch words with the physical route gates gives a well-formed
adjoint circuit. -/
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

/-- The ideal four-route word is well formed when `F` is an isometry. -/
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

/-- The native single-control four-route word is well formed when `F` is an isometry. -/
theorem word_wellFormed (F : Matrix H I ℂ) (hF : IsIsometry F)
    {P : Polynomial ℂ} (tables : PhaseTables P) : WellFormedAdjointCircuit (word F tables) :=
  compile_wellFormed _ _ (relabel_wellFormed _ _ (idealWord_wellFormed F hF tables))

/-- The native compression frame is an isometry whenever `F` is an isometry. -/
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

/-- Parallel lifting of two oracle matrices does not increase the norm of their difference. -/
theorem parallel_dist_le (C D : Matrix H H ℂ) :
    ‖parallelOracle (J:=J) C - parallelOracle (J:=J) D‖ ≤ ‖C-D‖ := by
  have he : parallelOracle (J:=J) C - parallelOracle (J:=J) D
      = (1 : Matrix J J ℂ) ⊗ₖ (C-D) := by
    rw [parallelOracle_eq_kronecker, parallelOracle_eq_kronecker, kronecker_sub_right]
  rw [he, l2_norm_kronecker]
  exact (mul_le_mul_of_nonneg_right
    (unitary_norm_le_one (U := (1 : Matrix J J ℂ)) (unitaryGroup J ℂ).one_mem)
    (norm_nonneg (C-D))).trans_eq (one_mul _)

/-- For unitary oracles within `δ ≥ 0`, compressing a well-formed parallel-oracle word between
isometric frames gives error at most its query count times `δ`. -/
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

/-- With unitary controlled-oracle error at most `δ ≥ 0`, the native word is unitary and its
isometric compression approximates `aeval A P` within the total phase-list length times `δ`,
with the stated query, fixed-gate, and five-flag counts. -/
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

/-- The paid native word's gate count is its compiled fixed-gate cost plus the total phase-list
length times the oracle-body gate count. -/
theorem paid_word_cost (F : Matrix H I ℂ) {P : Polynomial ℂ} (tables : PhaseTables P)
    (C : Matrix (Bool × H) (Bool × H) ℂ)
    (body : GateCompilation (parallelOracle (J:=Header) C))
    (compiler : GateCompiler (Work Header H)) :
    GateCount (paidAdjointCircuit body compiler (word F tables)) =
      paidAdjointFixedGateCost compiler (word F tables) +
        (∑ b : Bool, ∑ c : Bool, (tables.phases b c).length) * GateCount body.circuit := by
  rw [paid_adjoint_compiler_gate_count,(word_counts F tables).1]

omit [DecidableEq I] in

/-- The reversed paid native word has the same gate count: compiled fixed-gate cost plus the
total phase-list length times the oracle-body gate count. -/
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

/-- For unitary controlled-oracle error at most `δ ≥ 0` and a `KnownGateApproximation` with
error `η`, the compressed numerical word's error is at most `L*δ + (5*L+13)*η`, where `L` is
the total phase-list length. -/
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

/-- For nonnegative oracle and known-gate error bounds `δ` and `η`, the numerical word gives a
scale-one block encoding of `aeval A P` with error `L*δ + (5*L+13)*η`, where `L` is the
total phase-list length. -/
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

/-- With a unitary oracle body and gate compiler, running the paid native circuit with identity
oracle equals applying the native word evaluated at the parallel hardware oracle. -/
theorem paid_word_semantics (F : Matrix H I ℂ) {P : Polynomial ℂ} (tables : PhaseTables P)
    (C : Matrix (Bool × H) (Bool × H) ℂ) (hC : C ∈ unitaryGroup (Bool × H) ℂ)
    (body : GateCompilation (parallelOracle (J:=Header) C))
    (hbody : IsUnitaryCircuit body.circuit) (compiler : GateCompiler (Work Header H))
    (ψ : QState (Work Header H)) :
    Run 1 (paidAdjointCircuit body compiler (word F tables)) ψ =
      ApplyGate (evaluate (parallelOracle (J:=Header) C) (word F tables)) ψ :=
  paid_adjoint_compiler_semantics body compiler (parallelOracle_unitary hC) hbody _ ψ

end Qatlib.Concepts.NonNormalSpec.ResolventWord.ComplexFourRouteLcu
