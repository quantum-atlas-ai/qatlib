/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NativeNumerics.PhaseSynthesis.FinitePhaseSynthesis
import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed
import Qatlib.Concepts.CopyEvolution.Discriminate.ParallelQSVT
import Qatlib.Concepts.QspSimulation.Achievability.RealPartQSVT
import Qatlib.Concepts.CoherentSim.CoherentOAA.OddApproximation
import Qatlib.Concepts.SignalPrimitive.PhaseFrontend.SignPolynomial

/-!
# Computed Phase Matrix Transforms

`computedPhaseWord` turns finite rational phase synthesis output into an adjoint-query circuit
for the real-polynomial transformation framework of [GilyenSuLowWiebe2019]. For a bounded
rational polynomial of degree at most `d` and matching parity, successful synthesis gives an
actual approximate matrix transform with `d` queries and `d + 1` gates. Odd parity transforms
between the input and output frames; even parity gives a right singular transform using the
adjoint oracle.

Rational coefficient-list arithmetic represents `signPolynomial` exactly. Applying synthesized
phases to this family approximates the polar partial isometry when positive singular values have
gap `delta`, with block error `signPolynomialError delta k + eps` and query count `3^k`.

## Main statements

* `computed_phase_word_actual_matrix_transform` connects successful synthesis to a matrix block
  encoding.
* `realTarget_add`, `realTarget_sub`, and `realTarget_mul` justify rational coefficient
  arithmetic.
- `rationalSignCoefficients_semantics` identifies the generated sign polynomial.
- `computed_phase_word_actual_polar_consumer` gives the gap-dependent polar transform.

## References

* [Gilyen et al., 2019][GilyenSuLowWiebe2019], *Quantum singular value transformation and
  beyond: exponential improvements for quantum matrix arithmetics*.
-/

open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Matrix Polynomial
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- Compiles the Gaussian-rational base and phase list in `PhaseData` into a real-part QSVT
adjoint-query word for projectors `P` and `Q`. -/
noncomputable def computedPhaseWord {H : Type} [Fintype H] [DecidableEq H]
    (P Q : Matrix H H ℂ) (data : PhaseData) : List (AdjointStep (Bool × H)) :=
  compileRealPartQSVT P Q (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)

/-- Unit-norm assumptions on the base and listed Gaussian-rational values imply that all their
complex interpretations satisfy `IsPhase`. -/
theorem data_phase_valid (data : PhaseData) (hb : ‖gaussianRatComplex data.base‖ = 1)
    (hz : ∀ z ∈ data.phases,‖gaussianRatComplex z‖ = 1) :
    IsPhase (gaussianRatComplex data.base) ∧ ∀ z ∈ data.phases.map gaussianRatComplex,IsPhase z := by
  refine ⟨Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.isPhase_iff_normSq.mpr (by rw [Complex.normSq_eq_norm_sq,hb]; norm_num),?_⟩
  intro z hz'
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz'
  exact Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.isPhase_iff_normSq.mpr
      (by rw [Complex.normSq_eq_norm_sq,hz a ha]; norm_num)

/-- For a projected unitary encoding, positive rational tolerance `eps`, and a rational
polynomial bounded by one on `[-1, 1]` with degree at most `d` and matching parity, finite
phase synthesis succeeds and yields a well-formed circuit with `d` queries and `d + 1`
gates. Its odd or even singular transform has block error at most `eps`, giving a
computed-phase realization of real-polynomial QSVT from [GilyenSuLowWiebe2019]. -/
theorem computed_phase_word_actual_matrix_transform : ∀ (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (p : List ℚ) (d : ℕ) (eps : ℚ),
  ProjectedUnitaryEncoding A U L R → 0<eps → (realTarget p).degree ≤ (d:WithBot ℕ) →
  Qatlib.Concepts.QspSimulation.Achievability.HasRealParity d (realTarget p) →
  (∀ x ∈ Set.Icc (-1:ℝ) 1, |(realTarget p).eval x| ≤ 1) →
  ∃ data : PhaseData, (finitePhaseSynthesis p d eps).value=some data ∧
    let cs := computedPhaseWord (rangeProjector R) (rangeProjector L) data
    WellFormedAdjointCircuit cs ∧ adjointQueryCount cs=d ∧ adjointGateCount cs=d+1 ∧
    (d%2=1 → BlockEncoding (oddSingularTransform A (fun x => (((realTarget p).eval x:ℝ):ℂ)))
      (evaluate (parallelOracle U) cs) (averageFrame L) (averageFrame R) 1 (eps:ℝ)) ∧
    (d%2=0 → BlockEncoding (rightSingularTransform A (fun x => (((realTarget p).eval x:ℝ):ℂ)))
      (evaluate (parallelOracle Uᴴ) (computedPhaseWord (rangeProjector L) (rangeProjector R) data))
      (averageFrame R) (averageFrame R) 1 (eps:ℝ))
 := by
  intro H I O _ _ _ _ _ _ A U L R p d eps henc heps hp hpar hbound
  obtain ⟨data,hdata,hlen,hbase,hphases,hscore,happrox,hstats⟩ :=
    finite_rational_phase_synthesis_terminates p d eps heps hp hpar hbound
  have hph := data_phase_valid data hbase hphases
  have hlen' : (data.phases.map gaussianRatComplex).length = d := by simp [hlen]
  have hE : (0:ℝ) ≤ eps := by exact_mod_cast heps.le
  have hscalar (i : Fin (Fintype.card I)) :
      ‖(((responseP (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)).eval (matrixSingularValues A i:ℂ)).re:ℂ)-
        (((realTarget p).eval (matrixSingularValues A i):ℝ):ℂ)‖ ≤ (eps:ℝ) := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    apply happrox
    have hs := encoded_singularValues_mem_unitInterval henc i.val
    exact ⟨by linarith [hs.1],hs.2⟩
  have hcount := counts_compileRealPartQSVT (rangeProjector R) (rangeProjector L)
    (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)
  refine ⟨data,hdata,compileRealPartQSVT_wellFormed (rangeProjector_isOrthogonalProjector henc.right_isometry)
    (rangeProjector_isOrthogonalProjector henc.left_isometry) hph.1 _ hph.2,
    by simpa only [hlen',computedPhaseWord] using hcount.1,
    by simpa only [hlen',computedPhaseWord] using hcount.2,?_,?_⟩
  · intro hodd
    have hactual := realPartQSVT_odd_singularEncoding henc hph.1 (data.phases.map gaussianRatComplex) hph.2
      (by simpa only [hlen'] using hodd)
    have he : ‖oddSingularTransform A (fun x => (((realTarget p).eval x:ℝ):ℂ))-
        oddSingularTransform A (fun x => (((responseP (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)).eval (x:ℂ)).re:ℂ))‖ ≤ (eps:ℝ) :=
      oddSingularTransform_error_le A _ _ hE (fun i => by rw [norm_sub_rev]; exact hscalar i)
    simpa only [zero_add,computedPhaseWord,evaluate_compileRealPartQSVT] using
        (Qatlib.Concepts.BlockEncoding.ProjectedUnitaryEncoding.toBlockEncoding hactual).perturb hE he
  · intro heven
    have hactual := realPartQSVT_even_right_singularEncoding henc hph.1 (data.phases.map gaussianRatComplex) hph.2
      (by simpa only [hlen'] using heven)
    have he : ‖rightSingularTransform A (fun x => (((realTarget p).eval x:ℝ):ℂ))-
        rightSingularTransform A (fun x => (((responseP (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)).eval (x:ℂ)).re:ℂ))‖ ≤ (eps:ℝ) :=
      rightSingularTransform_error_le A _ _ hE (fun i => by rw [norm_sub_rev]; exact hscalar i)
    simpa only [zero_add,computedPhaseWord,evaluate_compileRealPartQSVT] using
        (Qatlib.Concepts.BlockEncoding.ProjectedUnitaryEncoding.toBlockEncoding hactual).perturb hE he

/-- Adds rational polynomial coefficient lists termwise, retaining the unmatched tail of the
longer list. -/
def ratAddList : List ℚ → List ℚ → List ℚ
  | [],ys => ys | xs,[] => xs | x::xs,y::ys => (x+y)::ratAddList xs ys
/-- Subtracts rational polynomial coefficient lists termwise, negating any unmatched tail of the
second list. -/
def ratSubList : List ℚ → List ℚ → List ℚ
  | [],ys => ys.map Neg.neg | xs,[] => xs | x::xs,y::ys => (x-y)::ratSubList xs ys
/-- Multiplies rational polynomial coefficient lists by recursive convolution in ascending
coefficient order. -/
def ratMulList : List ℚ → List ℚ → List ℚ
  | [],_ => []
  | x::xs,ys => ratAddList (ys.map (fun y=>x*y)) (0::ratMulList xs ys)
/-- Builds rational coefficient lists for the iterated sign polynomial, starting from `[0, 1]`
and applying the recurrence `(3*p - p^3)/2`. -/
def rationalSignCoefficients : ℕ → List ℚ
  | 0 => [0,1]
  | k+1 => let a := rationalSignCoefficients k
    (ratSubList (a.map (fun x=>3*x)) (ratMulList (ratMulList a a) a)).map (fun x=>x/2)

/-- The empty rational coefficient list represents the zero real polynomial. -/
@[simp] theorem realTarget_nil : realTarget [] = 0 := by simp [realTarget]

/-- Prepending coefficient `x` represents the polynomial `C x + X * realTarget xs`. -/
theorem realTarget_cons (x : ℚ) (xs : List ℚ) : realTarget (x::xs) = C (x:ℝ)+X*realTarget xs := by
  ext i
  cases i with
  | zero => simp [realTarget_coeff]
  | succ i => simp [realTarget_coeff,Polynomial.coeff_X_mul]

/-- Coefficient-list addition represents addition of the corresponding real target polynomials. -/
theorem realTarget_add (xs ys : List ℚ) : realTarget (ratAddList xs ys) = realTarget xs+realTarget ys := by
  induction xs generalizing ys with
  | nil => simp [ratAddList]
  | cons x xs ih =>
    cases ys with
    | nil => simp [ratAddList]
    | cons y ys =>
      rw [ratAddList,realTarget_cons,realTarget_cons,realTarget_cons,ih,Rat.cast_add,Polynomial.C_add]
      ring

/-- Scaling every rational coefficient by `c` multiplies the represented real polynomial by the
constant polynomial `C c`. -/
theorem realTarget_scale (c : ℚ) (xs : List ℚ) : realTarget (xs.map (fun x => c*x)) = C (c:ℝ)*realTarget xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons,realTarget_cons,realTarget_cons,ih,Rat.cast_mul,Polynomial.C_mul]
    ring

/-- Dividing every rational coefficient by `c` multiplies the represented real polynomial by the
constant polynomial corresponding to the rational reciprocal of `c`. -/
theorem realTarget_div (c : ℚ) (xs : List ℚ) : realTarget (xs.map (fun x => x/c)) = C ((1/c:ℚ):ℝ)*realTarget xs := by
  have he : xs.map (fun x => x/c) = xs.map (fun x => (1/c)*x) := by congr 1; funext x; ring
  rw [he,realTarget_scale]

/-- Coefficient-list subtraction represents subtraction of the corresponding real target
polynomials. -/
theorem realTarget_sub (xs ys : List ℚ) : realTarget (ratSubList xs ys) = realTarget xs-realTarget ys := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => simp [ratSubList]
    | cons y ys ih =>
      simp only [ratSubList,List.map_cons,realTarget_cons,Rat.cast_neg,Polynomial.C_neg]
      rw [show realTarget (ys.map Neg.neg) = -realTarget ys by simpa [ratSubList] using ih,realTarget_nil]
      ring
  | cons x xs ih =>
    cases ys with
    | nil => simp [ratSubList]
    | cons y ys =>
      rw [ratSubList,realTarget_cons,realTarget_cons,realTarget_cons,ih,Rat.cast_sub,Polynomial.C_sub]
      ring

/-- Coefficient-list convolution represents multiplication of the corresponding real target
polynomials. -/
theorem realTarget_mul (xs ys : List ℚ) : realTarget (ratMulList xs ys) = realTarget xs*realTarget ys := by
  induction xs with
  | nil => simp [ratMulList]
  | cons x xs ih =>
    rw [ratMulList,realTarget_add,realTarget_scale,realTarget_cons,realTarget_cons,ih]
    simp only [Rat.cast_zero,Polynomial.C_0,zero_add]
    ring

/-- The rational coefficient list generated at step `k` represents exactly `signPolynomial k`. -/
theorem rationalSignCoefficients_semantics (k : ℕ) : realTarget (rationalSignCoefficients k) = signPolynomial k := by
  induction k with
  | zero => simp [rationalSignCoefficients,realTarget_cons]
  | succ k ih =>
    rw [rationalSignCoefficients,realTarget_div,realTarget_sub,realTarget_scale,realTarget_mul,realTarget_mul,ih,signPolynomial]
    norm_num
    ring

/-- For a projected unitary encoding and positive rational tolerance `eps`, if every positive
singular value is at least `delta` with `0 < delta ≤ 1`, finite synthesis for the rational
sign polynomial yields a block encoding of the polar partial isometry with error
`signPolynomialError delta k + eps`. The circuit uses `3^k` queries and `3^k + 1` gates,
providing an explicit polynomial consumer of the singular-vector transformation framework of
[GilyenSuLowWiebe2019]. -/
theorem computed_phase_word_actual_polar_consumer : ∀ (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (delta : ℝ) (k : ℕ) (eps : ℚ),
  ProjectedUnitaryEncoding A U L R → 0<delta → delta≤1 → 0<eps →
  (∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i → delta ≤ matrixSingularValues A i) →
  realTarget (rationalSignCoefficients k)=signPolynomial k ∧
  (∃ data : PhaseData, (finitePhaseSynthesis (rationalSignCoefficients k) (3^k) eps).value=some data ∧
    let cs := computedPhaseWord (rangeProjector R) (rangeProjector L) data
    BlockEncoding (oddSingularTransform A (fun _ => 1)) (evaluate (parallelOracle U) cs)
      (averageFrame L) (averageFrame R) 1 (signPolynomialError delta k+(eps:ℝ)) ∧
    adjointQueryCount cs=3^k ∧ adjointGateCount cs=3^k+1)
 := by
  intro H I O _ _ _ _ _ _ A U L R delta k eps henc hdelta hdelta1 heps hgap
  have hpoly := rationalSignCoefficients_semantics k
  have hp : (realTarget (rationalSignCoefficients k)).degree ≤ ((3^k:ℕ):WithBot ℕ) := by
    rw [hpoly]
    exact Polynomial.natDegree_le_iff_degree_le.mp (by rw [signPolynomial_natDegree])
  have hodd : Odd (3^k:ℕ) := (by decide : Odd 3).pow
  have hpar : Qatlib.Concepts.QspSimulation.Achievability.HasRealParity (3^k) (realTarget (rationalSignCoefficients k)) := by
    rw [hpoly]
    unfold Qatlib.Concepts.QspSimulation.Achievability.HasRealParity
    rw [signPolynomial_comp_neg_X,hodd.neg_one_pow,Polynomial.C_neg,Polynomial.C_1,neg_mul,one_mul]
  have hb : ∀ x ∈ Set.Icc (-1:ℝ) 1, |(realTarget (rationalSignCoefficients k)).eval x| ≤ 1 := by
    rw [hpoly]
    exact fun x hx => signPolynomial_abs_le_one k hx
  obtain ⟨data,hdata,hWF,hquery,hgate,hoddEnc,hevenEnc⟩ :=
    computed_phase_word_actual_matrix_transform H I O A U L R (rationalSignCoefficients k) (3^k) eps henc heps hp hpar hb
  have he : (0:ℝ) ≤ signPolynomialError delta k := by
    unfold signPolynomialError
    apply pow_nonneg
    nlinarith
  have herr : ‖oddSingularTransform A (fun _ => (1:ℂ))-
      oddSingularTransform A (fun x => (((realTarget (rationalSignCoefficients k)).eval x:ℝ):ℂ))‖ ≤ signPolynomialError delta k := by
    apply oddSingularTransform_error_le_positive A _ _ he
    intro i hi
    rw [show (1:ℂ) = ((1:ℝ):ℂ) by rfl,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,hpoly]
    have h := signPolynomial_error_le k hdelta (by rw [abs_of_pos hi]; exact hgap i hi)
      (by rw [abs_of_pos hi]; exact (encoded_singularValues_mem_unitInterval henc i.val).2)
    simpa only [Real.sign_of_pos hi] using h
  refine ⟨hpoly,data,hdata,?_,hquery,hgate⟩
  have hactual := hoddEnc (by norm_num [Nat.pow_mod])
  simpa only [add_comm] using hactual.perturb he herr

end Qatlib.Concepts.SignalPrimitive.PhaseFrontend
