/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.Structure.Theorem9Stat
import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem5Quan
import Qatlib.Papers.QLinearODE17.Structure.Theorem9Encoding

/-!
# Inverse-word guarantees for the Taylor linear system

This module derives singular-value gaps from left-inverse bounds and applies the finite
inverse-word construction to a solved linear system. It gives explicit query and gate counts,
normalized output error, and a postselection probability bound.

For the V2 Taylor matrix, `taylorV2_encoding_and_gap` combines diagonalizability, stability,
norm, and sparsity hypotheses to produce a bounded positive integer gap parameter and a sparse
overlap encoding. This supplies the linear-system step in the ODE algorithm of
[BerryEtAl2017ODE].

## Main statements

* `taylor_actual_inverse_word_of_solved`: Finite inverse-word counts, output accuracy, and
  postselection bound.
* `taylor_scaled_inverse`: Two-sided inverse identities for the scaled Taylor matrix.
* `taylorV2_encoding_and_gap`: A bounded integer gap parameter and sparse overlap encoding.

## References

* [Berry et al., 2017][BerryEtAl2017ODE]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution Qatlib.Papers.QLinearODE17.TaylorAnalysis
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QLinearODE17.StructureCore
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped BigOperators Matrix.Norms.L2Operator
set_option warningAsError false

variable {I : Type} [Fintype I] [DecidableEq I]

/-- If `B * A = 1`, κ is positive, and ‖B‖ ≤ κ, every positive singular value of `A` is at least
1/κ. -/
theorem taylor_singular_gap_of_left_inverse (A B : Matrix I I ℂ) (hBA : B*A=1)
    (κ : ℕ) (hκ : 0 < κ) (hB : ‖B‖ ≤ (κ : ℝ))
    (i : Fin (Fintype.card I)) (hσ : 0 < matrixSingularValues A i) :
    (κ : ℝ)⁻¹ ≤ matrixSingularValues A i := by
  let v : QState I := WithLp.ofLp (rightSingularBasis A i)
  have hv : ‖stateVector v‖=1 := norm_rightSingularBasis A i
  have hAv : ‖stateVector (A *ᵥ v)‖=matrixSingularValues A i := by
    exact norm_apply_rightSingularBasis A i
  have hback : B *ᵥ (A *ᵥ v)=v := by rw [Matrix.mulVec_mulVec,hBA,Matrix.one_mulVec]
  have hn := stateVector_mulVec_norm_le B (A *ᵥ v)
  rw [hback,hv,hAv] at hn
  have hn' : 1 ≤ (κ : ℝ)*matrixSingularValues A i :=
    hn.trans (mul_le_mul_of_nonneg_right hB hσ.le)
  have hκR : (0 : ℝ) < κ := by exact_mod_cast hκ
  rw [inv_eq_one_div]
  exact (div_le_iff₀ hκR).mpr (by simpa only [mul_comm] using! hn')

variable {H : Type} [Fintype H] [DecidableEq H]

/-- For a projected unitary encoding with the stated singular-value gap and a normalized
right-hand side `z = A *ᵥ y`, the finite inverse word has the explicit query and gate
counts. It produces a normalized postselected state within 2^(-k) of normalized `y`, with
the stated postselection lower bound. -/
theorem taylor_actual_inverse_word_of_solved (A B : Matrix I I ℂ)
    (U : Matrix H H ℂ) (L R : Matrix H I ℂ) (κ k : ℕ) (z y : QState I)
    (henc : ProjectedUnitaryEncoding A U L R) (hκ : 0 < κ) (hz : Normalized z)
    (hgap : ∀ i : Fin (Fintype.card I),0 < matrixSingularValues A i →
      (κ : ℝ)⁻¹ ≤ matrixSingularValues A i)
    (hBA : B*A=1) (hy : A *ᵥ y=z) :
    let nq := explicitInverseCutoff κ (k+2)
    let word := finiteInverseWord L R κ k
    let W := evaluate (parallelOracle U) word
    adjointQueryCount word=2*nq-1 ∧ adjointGateCount word=2*nq+2 ∧
    ∃ φ : QState I,
      postselectionOutput W (coordinatePhaseFrame R) (coordinatePhaseFrame L) z=some φ ∧
      Normalized φ ∧ ‖stateVector φ-NormedSpace.normalize (stateVector y)‖ ≤ (1 : ℝ)/2^k ∧
      postselectionProbability W (coordinatePhaseFrame R) (coordinatePhaseFrame L) z ≥
        (1-(1 : ℝ)/2^k/2)^2/(16*(nq : ℝ)) := by
  (try dsimp only)
  have hrange : ∃ y : QState I,A *ᵥ y=z := ⟨y,hy⟩
  have hτ : leastSquaresOverlap A z=1 := by
    unfold leastSquaresOverlap
    rw [← Matrix.mulVec_mulVec,matrixPseudoinverse_mulVec_solves A z hrange]
    exact (normalized_iff_stateVector_norm z).mp hz
  have ht : (1/2 : ℝ)^k < 2*leastSquaresOverlap A z := by
    rw [hτ]
    have := (inverse_precision_interval k).2
    linarith
  obtain ⟨hprob,φ,hout,x,hLS,_,hφ,herr⟩ :=
    (computed_inverse_actual_least_squares_and_zero H I I A U L R κ k z henc hκ hz hgap).1 ht
  have hxy : x=y := by
    have hres := hLS.1 y
    rw [hy,sub_self] at hres
    rw [show stateVector (0 : QState I)=0 from rfl,norm_zero] at hres
    have hzero : stateVector (A *ᵥ x-z)=0 := by
      apply norm_eq_zero.mp
      apply le_antisymm
      · exact hres
      · exact norm_nonneg _
    have hx : A *ᵥ x=z := sub_eq_zero.mp ((stateVector_eq_zero_iff _).mp hzero)
    calc x=B *ᵥ (A *ᵥ x) := by rw [Matrix.mulVec_mulVec,hBA,Matrix.one_mulVec]
      _=B *ᵥ (A *ᵥ y) := by rw [hx,hy]
      _=y := by rw [Matrix.mulVec_mulVec,hBA,Matrix.one_mulVec]
  have hw := computed_full_inverse_actual_encoding_and_cost H I I A U L R κ k henc hκ hgap
  refine ⟨hw.2.2.2.1,hw.2.2.2.2,φ,hout,hφ,?_,?_⟩
  · rw [hxy,hτ,div_one] at herr
    simpa only [_root_.one_div_pow] using! herr
  · rw [hτ] at hprob
    simpa only [_root_.one_div_pow] using! hprob

/-- For κV ≥ 1, k ≥ 5, and p > 0, there is a positive integer κ between 3κV√k(m + p)(k + s + 3)
and 6κV k(m + p)(k + s + 3). -/
theorem taylor_integer_kappa (m k p s : ℕ) (κV : ℝ) (hκV : 1 ≤ κV)
    (hk : 5 ≤ k) (hp : 0 < p) :
    ∃ κ : ℕ,0 < κ ∧
      (κ : ℝ) ≤ 6*κV*(k : ℝ)*((m+p : ℕ) : ℝ)*((k+s+3 : ℕ) : ℝ) ∧
      3*κV*Real.sqrt (k : ℝ)*((m+p : ℕ) : ℝ)*((k+s+3 : ℕ) : ℝ) ≤ κ := by
  let T : ℝ := κV*((m+p : ℕ) : ℝ)*((k+s+3 : ℕ) : ℝ)
  have hmp : (1 : ℝ) ≤ (m+p : ℕ) := by exact_mod_cast (show 1 ≤ m+p by omega)
  have hs : (1 : ℝ) ≤ (k+s+3 : ℕ) := by exact_mod_cast (show 1 ≤ k+s+3 by omega)
  have hT : 1 ≤ T := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hκV hmp) hs
  have hkR : (5 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by linarith
  have hsqrt : Real.sqrt (k : ℝ) ≤ k := by
    nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ k),Real.sqrt_nonneg (k : ℝ)]
  let a : ℝ := 3*Real.sqrt (k : ℝ)*T
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨Nat.ceil a,(Nat.one_le_ceil_iff.mpr ha).trans_lt' (by omega : 0 < 1),?_,?_⟩
  · have hceil := (Nat.ceil_lt_add_one ha.le).le
    have hbase : 1 ≤ 3*(k : ℝ)*T := one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num) hk1) hT
    have habound : a ≤ 3*(k : ℝ)*T := by dsimp [a]; gcongr
    calc
      (Nat.ceil a : ℝ) ≤ a+1 := hceil
      _ ≤ 6*(k : ℝ)*T := by nlinarith
      _ = _ := by dsimp [T]; ring
  · have hceil := Nat.le_ceil a
    calc
      _=a := by dsimp [a,T]; ring
      _ ≤ _ := hceil

variable {N : Type} [Fintype N] [DecidableEq N]

omit [DecidableEq N] in

/-- Real scalar multiplication preserves the stated upper bounds on the row and column sparsity
of `A`. -/
theorem taylor_scaled_data_sparse (A : Matrix N N ℂ) (h : ℝ) (s : ℕ)
    (hr : ∀ n,(Finset.univ.filter (fun c => A n c≠0)).card ≤ s)
    (hc : ∀ c,(Finset.univ.filter (fun n => A n c≠0)).card ≤ s) :
    (∀ n,(Finset.univ.filter (fun c => (h • A) n c≠0)).card ≤ s) ∧
    (∀ c,(Finset.univ.filter (fun n => (h • A) n c≠0)).card ≤ s) := by
  constructor
  · intro n
    apply (Finset.card_le_card ?_).trans (hr n)
    intro c hn
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hn ⊢
    intro hz
    exact hn (by simp [Matrix.smul_apply,hz])
  · intro c
    apply (Finset.card_le_card ?_).trans (hc c)
    intro n hn
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hn ⊢
    intro hz
    exact hn (by simp [Matrix.smul_apply,hz])

/-- Multiplying the inverse V2 Taylor matrix by k + s + 3 gives a two-sided inverse of the
Taylor matrix divided by k + s + 3. -/
theorem taylor_scaled_inverse (m k p s : ℕ) (M : Matrix N N ℂ) :
    (((k+s+3 : ℕ) : ℂ) • (taylorStepMatrixV2 m k p M)⁻¹) *
        (((k+s+3 : ℕ) : ℂ)⁻¹ • taylorStepMatrixV2 m k p M)=1 ∧
    (((k+s+3 : ℕ) : ℂ)⁻¹ • taylorStepMatrixV2 m k p M) *
        (((k+s+3 : ℕ) : ℂ) • (taylorStepMatrixV2 m k p M)⁻¹)=1 := by
  have hs : ((k+s+3 : ℕ) : ℂ)≠0 := by exact_mod_cast (show k+s+3≠0 by omega)
  rw [smul_mul_smul,smul_mul_smul,mul_inv_cancel₀ hs,inv_mul_cancel₀ hs,
    one_smul,one_smul]
  exact (taylorStepMatrixV2_inverse m k p M).symm

/-- Under the stated diagonalizability, stability, Taylor-parameter, and generator sparsity
assumptions, the scaled V2 Taylor matrix has a sparse overlap encoding and positive singular
values at least 1/κ for a positive integer κ with the explicit upper bound. -/
theorem taylorV2_encoding_and_gap [Nonempty N] (s m k p : ℕ) (A V D : Matrix N N ℂ)
    (h : ℝ) (hm : 0 < m) (hk : 5 ≤ k) (hp : 0 < p) (hh : 0 < h)
    (hfac : 2*m ≤ Nat.factorial (k+1))
    (hr : ∀ n,(Finset.univ.filter (fun c => A n c≠0)).card ≤ s)
    (hc : ∀ c,(Finset.univ.filter (fun n => A n c≠0)).card ≤ s)
    (hd : ∀ i j : N,i≠j → D i j=0) (hA : A=V*D*V⁻¹)
    (hV1 : V*V⁻¹=1) (hV2 : V⁻¹*V=1) (hre : ∀ n,(D n n).re ≤ 0) (hM : ‖h • A‖ ≤ 1) :
    ∃ κ : ℕ,0 < κ ∧
      (κ : ℝ) ≤ 6*(‖V‖*‖V⁻¹‖)*(k : ℝ)*((m+p : ℕ) : ℝ)*((k+s+3 : ℕ) : ℝ) ∧
      (∀ i : Fin (Fintype.card (Fin (m*(k+1)+p+1) × N)),
        0 < matrixSingularValues (((k+s+3 : ℕ) : ℂ)⁻¹ • taylorStepMatrixV2 m k p (h • A)) i →
          (κ : ℝ)⁻¹ ≤ matrixSingularValues (((k+s+3 : ℕ) : ℂ)⁻¹ • taylorStepMatrixV2 m k p (h • A)) i) ∧
      ProjectedUnitaryEncoding (((k+s+3 : ℕ) : ℂ)⁻¹ • taylorStepMatrixV2 m k p (h • A))
        (1 : Matrix _ _ ℂ)
        (sparseOverlapLeft (taylorStepMatrixV2 m k p (h • A)) (k+s+3))
        (sparseOverlapRight (taylorStepMatrixV2 m k p (h • A)) (k+s+3)) := by
  have hκV : 1 ≤ ‖V‖*‖V⁻¹‖ := by
    calc 1=‖(1 : Matrix N N ℂ)‖ := (norm_one : ‖(1 : Matrix N N ℂ)‖=1).symm
      _=‖V*V⁻¹‖ := by rw [hV1]
      _ ≤ _ := Matrix.l2_opNorm_mul _ _
  obtain ⟨κ,hκ,hbudget,hceil⟩ := taylor_integer_kappa m k p s (‖V‖*‖V⁻¹‖) hκV hk hp
  have hzD : ∀ n : N,‖(h • D) n n‖ ≤ 1 := by
    intro n
    simpa only [Matrix.smul_apply,Complex.real_smul] using!
      hA_eigen_norm_le A V D hA hV1 hV2 hd h hh hM n
  have hdD : ∀ i j : N,i≠j → (h • D) i j=0 := by
    intro i j hij
    simp [Matrix.smul_apply,hd i j hij]
  have hreD : ∀ n : N,((h • D) n n).re ≤ 0 := by
    intro n
    simpa only [Matrix.smul_apply,Complex.real_smul,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using!
      mul_nonpos_of_nonneg_of_nonpos hh.le (hre n)
  have hAV : (h • A)*V=V*(h • D) := by
    rw [Matrix.smul_mul,hA,Matrix.mul_assoc,hV2,mul_one,Matrix.mul_smul]
  have hInv := (taylorV2_inverse_norm_transport m k p (h • A) V (h • D) hAV hV1 hV2).trans
    (mul_le_mul_of_nonneg_left (taylorV2_diagonal_inverse_norm_le m k p (h • D) hm hk hp hfac hdD hzD hreD)
      (by positivity))
  have hB : ‖((k+s+3 : ℕ) : ℂ) • (taylorStepMatrixV2 m k p (h • A))⁻¹‖ ≤ (κ : ℝ) := by
    rw [norm_smul,Complex.norm_natCast]
    calc
      _ ≤ ((k+s+3 : ℕ) : ℝ)*((‖V‖*‖V⁻¹‖)*(3*Real.sqrt (k : ℝ)*((m+p : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hInv (by positivity)
      _ ≤ _ := by convert! hceil using 1; ring
  have hs := taylor_scaled_data_sparse A h s hr hc
  refine ⟨κ,hκ,hbudget,?_,(taylorV2_sparse_encoding s m k p (h • A) hM hs.1 hs.2).1⟩
  intro i hi
  exact taylor_singular_gap_of_left_inverse _ _
      (taylor_scaled_inverse m k p s (h • A)).1 κ hκ hB i hi

end Qatlib.Papers.QLinearODE17.StructureCore
