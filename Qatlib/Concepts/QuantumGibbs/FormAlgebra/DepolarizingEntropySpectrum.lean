/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.LindbladSemigroup
public import QuantumInfo.ForMathlib.HermitianMat.LogExp
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.WalkSearch.TwoLevelLower Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.DirichletForm.KmsDirichlet Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LindbladFlow.GkslSemigroup

namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra.DepolarizingEntropySpectrum

open Matrix Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.LindbladSemigroup
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open scoped InnerProductSpace RealInnerProductSpace

noncomputable def maximallyMixed : Operator 2 := (1 / 2 : ℝ) • 1

noncomputable def spectrumRadius (σ : Operator 2) : ℝ :=
  Matrix.traceNorm (σ - maximallyMixed)

/-- The inner product of a Hermitian two-by-two matrix with its logarithm is the sum of each
eigenvalue times its logarithm. -/
theorem hermitian_inner_log_self (A : HermitianMat (Fin 2) ℂ) :
    ⟪A, A.log⟫ = ∑ i, A.H.eigenvalues i * Real.log (A.H.eigenvalues i) := by
  rw [HermitianMat.inner_comm, HermitianMat.log, HermitianMat.inner_eq_re_trace]
  nth_rw 2 [← A.cfc_id]
  rw [← A.mat_cfc_mul]
  rw [← HermitianMat.trace_eq_re_trace, ← HermitianMat.sum_eigenvalues_eq_trace]
  obtain ⟨e, he⟩ := A.cfc_eigenvalues (Real.log * _root_.id)
  rw [he]
  simp only [Function.comp_apply, Pi.mul_apply, id_eq]
  rw [Equiv.sum_comp e (fun i =>
    Real.log (A.H.eigenvalues i) * A.H.eigenvalues i)]
  simp [mul_comm]

/-- For a Hermitian trace-one qubit operator, `spectrumRadius` is the absolute difference of its
two eigenvalues. -/
theorem spectrumRadius_eq_abs_eigenvalue_sub {σ : Operator 2}
    (hσ : σ.IsHermitian) (htr : Matrix.trace σ = 1) :
    spectrumRadius σ = |hσ.eigenvalues 0 - hσ.eigenvalues 1| := by
  let A : HermitianMat (Fin 2) ℂ := ⟨σ, hσ⟩
  let C : HermitianMat (Fin 2) ℂ := A - (1 / 2 : ℝ) • 1
  have hCcfc : C = A.cfc (fun x : ℝ => x - 1 / 2) := by
    dsimp [C]
    rw [HermitianMat.cfc_sub_apply, HermitianMat.cfc_id', HermitianMat.cfc_const]
  have hsum : A.H.eigenvalues 0 + A.H.eigenvalues 1 = 1 := by
    have h := A.sum_eigenvalues_eq_trace
    simpa [A, Fin.sum_univ_two, HermitianMat.trace_eq_re_trace, htr] using! h
  change Matrix.traceNorm C.mat = _
  rw [Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues C.H]
  obtain ⟨e, he⟩ := A.cfc_eigenvalues (fun x : ℝ => x - 1 / 2)
  have heig : C.H.eigenvalues =
      (fun x : ℝ => x - 1 / 2) ∘ A.H.eigenvalues ∘ e := by
    rw [hCcfc]
    exact he
  change ∑ i, |C.H.eigenvalues i| = |A.H.eigenvalues 0 - A.H.eigenvalues 1|
  rw [heig]
  simp only [Function.comp_apply]
  calc
    ∑ i, |A.H.eigenvalues (e i) - 1 / 2| =
        ∑ i, |A.H.eigenvalues i - 1 / 2| :=
      Equiv.sum_comp e (fun i => |A.H.eigenvalues i - 1 / 2|)
    _ = |A.H.eigenvalues 0 - A.H.eigenvalues 1| := by
      have h0 : A.H.eigenvalues 0 - 1 / 2 =
          (A.H.eigenvalues 0 - A.H.eigenvalues 1) / 2 := by linarith
      have h1 : A.H.eigenvalues 1 - 1 / 2 =
          -(A.H.eigenvalues 0 - A.H.eigenvalues 1) / 2 := by linarith
      rw [Fin.sum_univ_two, h0, h1, abs_div, abs_div, abs_neg]
      norm_num

/-- The maximally mixed qubit operator is a density operator. -/
theorem maximallyMixed_isDensity : IsDensityOperator maximallyMixed := by
  constructor
  · exact (Matrix.PosDef.one.smul (by norm_num : (0 : ℝ) < 1 / 2)).posSemidef
  · simp [maximallyMixed, Matrix.trace_smul, Matrix.trace_one]

/-- The maximally mixed qubit operator is positive definite. -/
theorem maximallyMixed_posDef : maximallyMixed.PosDef := by
  exact Matrix.PosDef.one.smul (by norm_num : (0 : ℝ) < 1 / 2)

/-- The relative entropy of a Hermitian trace-one qubit operator against the maximally mixed
operator is its eigenvalue-logarithm sum plus the logarithm of two. -/
theorem relativeEntropy_maximallyMixed_eq_spectralSum {σ : Operator 2}
    (hσ : σ.IsHermitian) (htr : Matrix.trace σ = 1) :
    relativeEntropy σ maximallyMixed =
      (∑ i, hσ.eigenvalues i * Real.log (hσ.eigenvalues i)) + Real.log 2 := by
  let A : HermitianMat (Fin 2) ℂ := ⟨σ, hσ⟩
  let R : HermitianMat (Fin 2) ℂ := (1 / 2 : ℝ) • 1
  have hRlog : R.log = Real.log (1 / 2) • (1 : HermitianMat (Fin 2) ℂ) := by
    dsimp [R]
    rw [HermitianMat.log_smul (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    simp
  have hRinner : ⟪A, R.log⟫ = Real.log (1 / 2) := by
    rw [hRlog, HermitianMat.inner_smul_right, HermitianMat.inner_one,
      (A.trace_eq_one_iff).mpr htr, mul_one]
  change ⟪A, A.log - R.log⟫ = _
  rw [inner_sub_right, hermitian_inner_log_self, hRinner]
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    norm_num
  rw [hlog, sub_neg_eq_add]

/-- The function `twoLevelMix` is unchanged by replacing its argument with its absolute value. -/
theorem twoLevelMix_abs (s : ℝ) : twoLevelMix |s| = twoLevelMix s := by
  rcases le_total 0 s with hs | hs
  · rw [abs_of_nonneg hs]
  · rw [abs_of_nonpos hs, twoLevelMix_even]

/-- For two real numbers summing to one, `twoLevelMix` of their difference is their
eigenvalue-logarithm sum plus the logarithm of two. -/
theorem twoLevelMix_sub_of_add_eq_one {a b : ℝ} (hab : a + b = 1) :
    twoLevelMix (a - b) = a * Real.log a + b * Real.log b + Real.log 2 := by
  by_cases ha : a = 0
  · have hb : b = 1 := by linarith
    simp [ha, hb, twoLevelMix]
    norm_num
  by_cases hb : b = 0
  · have ha1 : a = 1 := by linarith
    simp [ha1, hb, twoLevelMix]
    norm_num
  have hpa : 1 + (a - b) = 2 * a := by linarith
  have hpb : 1 - (a - b) = 2 * b := by linarith
  have hca : (2 * a) / 2 = a := by ring
  have hcb : (2 * b) / 2 = b := by ring
  unfold twoLevelMix
  rw [hpa, hpb, hca, hcb, Real.log_mul (by norm_num) ha,
    Real.log_mul (by norm_num) hb]
  calc
    a * (Real.log 2 + Real.log a) + b * (Real.log 2 + Real.log b) =
        (a + b) * Real.log 2 + (a * Real.log a + b * Real.log b) := by ring
    _ = _ := by rw [hab]; ring

/-- The relative entropy of a Hermitian trace-one qubit operator against the maximally mixed
operator equals `twoLevelMix` of its spectral radius. -/
theorem relativeEntropy_maximallyMixed_eq_twoLevelMix {σ : Operator 2}
    (hσ : σ.IsHermitian) (htr : Matrix.trace σ = 1) :
    relativeEntropy σ maximallyMixed = twoLevelMix (spectrumRadius σ) := by
  let A : HermitianMat (Fin 2) ℂ := ⟨σ, hσ⟩
  have hsum : A.H.eigenvalues 0 + A.H.eigenvalues 1 = 1 := by
    have h := A.sum_eigenvalues_eq_trace
    simpa [A, Fin.sum_univ_two, HermitianMat.trace_eq_re_trace, htr] using! h
  rw [relativeEntropy_maximallyMixed_eq_spectralSum hσ htr,
    spectrumRadius_eq_abs_eigenvalue_sub hσ htr, twoLevelMix_abs]
  change (∑ i, A.H.eigenvalues i * Real.log (A.H.eigenvalues i)) + Real.log 2 = _
  rw [Fin.sum_univ_two]
  exact (twoLevelMix_sub_of_add_eq_one hsum).symm

/-- The relative entropy of a qubit density operator against the maximally mixed state equals
`twoLevelMix` of its spectral radius. -/
theorem relativeEntropy_density_eq_twoLevelMix {σ : Operator 2}
    (hσ : IsDensityOperator σ) :
    relativeEntropy σ maximallyMixed = twoLevelMix (spectrumRadius σ) :=
  relativeEntropy_maximallyMixed_eq_twoLevelMix hσ.1.1 hσ.2

/-- The spectral radius `spectrumRadius` is nonnegative. -/
theorem spectrumRadius_nonneg (σ : Operator 2) : 0 ≤ spectrumRadius σ := by
  exact Matrix.traceNorm_nonneg _

/-- The spectral radius of a qubit density operator is at most one. -/
theorem spectrumRadius_le_one {σ : Operator 2} (hσ : IsDensityOperator σ) :
    spectrumRadius σ ≤ 1 := by
  let A : HermitianMat (Fin 2) ℂ := ⟨σ, hσ.1.1⟩
  have hsum : A.H.eigenvalues 0 + A.H.eigenvalues 1 = 1 := by
    have h := A.sum_eigenvalues_eq_trace
    simpa [A, Fin.sum_univ_two, HermitianMat.trace_eq_re_trace, hσ.2] using! h
  have h0 := hσ.1.eigenvalues_nonneg 0
  have h1 := hσ.1.eigenvalues_nonneg 1
  change 0 ≤ A.H.eigenvalues 0 at h0
  change 0 ≤ A.H.eigenvalues 1 at h1
  rw [spectrumRadius_eq_abs_eigenvalue_sub hσ.1.1 hσ.2]
  exact (abs_le).mpr ⟨by change -1 ≤ A.H.eigenvalues 0 - A.H.eigenvalues 1; linarith,
    by change A.H.eigenvalues 0 - A.H.eigenvalues 1 ≤ 1; linarith⟩

/-- The spectral radius of a positive definite qubit density operator is strictly less than one. -/
theorem spectrumRadius_lt_one {σ : Operator 2}
    (hσ : IsDensityOperator σ) (hσfull : σ.PosDef) : spectrumRadius σ < 1 := by
  let A : HermitianMat (Fin 2) ℂ := ⟨σ, hσ.1.1⟩
  have hsum : A.H.eigenvalues 0 + A.H.eigenvalues 1 = 1 := by
    have h := A.sum_eigenvalues_eq_trace
    simpa [A, Fin.sum_univ_two, HermitianMat.trace_eq_re_trace, hσ.2] using! h
  have h0 := hσfull.eigenvalues_pos 0
  have h1 := hσfull.eigenvalues_pos 1
  change 0 < A.H.eigenvalues 0 at h0
  change 0 < A.H.eigenvalues 1 at h1
  rw [spectrumRadius_eq_abs_eigenvalue_sub hσ.1.1 hσ.2]
  exact (abs_lt).mpr ⟨by change -1 < A.H.eigenvalues 0 - A.H.eigenvalues 1; linarith,
    by change A.H.eigenvalues 0 - A.H.eigenvalues 1 < 1; linarith⟩

/-- On the interval from zero to one, `twoLevelMix` is at least one half the square of its
argument. -/
theorem twoLevelMix_ge_half_sq_of_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s ^ 2 / 2 ≤ twoLevelMix s := by
  rcases eq_or_lt_of_le hs1 with rfl | hs
  · have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.log_two_gt_d9
      norm_num at h
      linarith
    norm_num [twoLevelMix]
    exact hlog
  · exact twoLevelMix_ge_half_sq hs0 hs

/-- The relative entropy of a qubit density operator against the maximally mixed state is
nonnegative. -/
theorem relativeEntropy_maximallyMixed_nonneg {σ : Operator 2}
    (hσ : IsDensityOperator σ) : 0 ≤ relativeEntropy σ maximallyMixed := by
  rw [relativeEntropy_density_eq_twoLevelMix hσ]
  have h := twoLevelMix_ge_half_sq_of_le (spectrumRadius_nonneg σ)
    (spectrumRadius_le_one hσ)
  nlinarith [sq_nonneg (spectrumRadius σ)]

/-- The trace distance of a qubit density operator from the maximally mixed state is at most the
square root of twice their relative entropy. -/
theorem traceDistance_le_sqrt_two_relativeEntropy {σ : Operator 2}
    (hσ : IsDensityOperator σ) :
    traceDistance σ maximallyMixed ≤
      Real.sqrt (2 * relativeEntropy σ maximallyMixed) := by
  rw [relativeEntropy_density_eq_twoLevelMix hσ]
  change spectrumRadius σ / 2 ≤ Real.sqrt (2 * twoLevelMix (spectrumRadius σ))
  apply Real.le_sqrt_of_sq_le
  have h := twoLevelMix_ge_half_sq_of_le (spectrumRadius_nonneg σ)
    (spectrumRadius_le_one hσ)
  nlinarith

/-- The maximally mixed qubit operator is Hermitian. -/
theorem maximallyMixed_hermitian : maximallyMixed.IsHermitian := by
  exact Matrix.isHermitian_one.smul (R := ℝ) (IsSelfAdjoint.all _)

/-- The depolarizing semigroup sends a trace-one operator to the maximally mixed operator plus
its exponentially scaled deviation. -/
theorem depolarizing_orbit (γ : ℝ) (hγ : 0 ≤ γ) (t : ℝ) {τ : Operator 2}
    (htr : Matrix.trace τ = 1) :
    lindbladSemigroup (depolarizingGKSL γ) t τ =
      maximallyMixed + ((Real.exp (-(γ * t)) : ℝ) : ℂ) • (τ - maximallyMixed) := by
  rw [lindbladSemigroup_depolarizing_apply γ hγ t τ, htr]
  ext i j
  simp [maximallyMixed, Matrix.smul_apply, RCLike.real_smul_eq_coe_smul]

/-- The depolarizing semigroup preserves Hermiticity of trace-one qubit operators. -/
theorem depolarizing_orbit_hermitian (γ : ℝ) (hγ : 0 ≤ γ) (t : ℝ) {τ : Operator 2}
    (hτ : τ.IsHermitian) (htr : Matrix.trace τ = 1) :
    (lindbladSemigroup (depolarizingGKSL γ) t τ).IsHermitian := by
  rw [depolarizing_orbit γ hγ t htr]
  apply maximallyMixed_hermitian.add
  apply (hτ.sub maximallyMixed_hermitian).smul
  exact Complex.conj_ofReal _

/-- The depolarizing semigroup preserves trace one. -/
theorem depolarizing_orbit_trace (γ : ℝ) (t : ℝ) {τ : Operator 2}
    (htr : Matrix.trace τ = 1) :
    Matrix.trace (lindbladSemigroup (depolarizingGKSL γ) t τ) = 1 := by
  rw [trace_lindbladSemigroup, htr]

/-- The spectral radius along a trace-one depolarizing orbit is the initial spectral radius
multiplied by the decay exponential. -/
theorem spectrumRadius_depolarizing_orbit (γ : ℝ) (hγ : 0 ≤ γ) (t : ℝ) {τ : Operator 2}
    (htr : Matrix.trace τ = 1) :
    spectrumRadius (lindbladSemigroup (depolarizingGKSL γ) t τ) =
      Real.exp (-(γ * t)) * spectrumRadius τ := by
  unfold spectrumRadius
  rw [depolarizing_orbit γ hγ t htr, add_sub_cancel_left,
    Matrix.traceNorm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_pos _).le]

/-- The relative entropy along a Hermitian trace-one depolarizing orbit equals `twoLevelMix` of
the exponentially decaying spectral radius. -/
theorem relativeEntropy_depolarizing_orbit (γ : ℝ) (hγ : 0 ≤ γ) (t : ℝ) {τ : Operator 2}
    (hτ : τ.IsHermitian) (htr : Matrix.trace τ = 1) :
    relativeEntropy (lindbladSemigroup (depolarizingGKSL γ) t τ) maximallyMixed =
      twoLevelMix (Real.exp (-(γ * t)) * spectrumRadius τ) := by
  rw [relativeEntropy_maximallyMixed_eq_twoLevelMix
    (depolarizing_orbit_hermitian γ hγ t hτ htr) (depolarizing_orbit_trace γ t htr),
    spectrumRadius_depolarizing_orbit γ hγ t htr]

/-- The exponentially scaled spectral radius is nonnegative. -/
theorem exp_mul_spectrumRadius_nonneg (γ t : ℝ) (τ : Operator 2) :
    0 ≤ Real.exp (-(γ * t)) * spectrumRadius τ := by
  exact mul_nonneg (Real.exp_pos _).le (spectrumRadius_nonneg τ)

/-- For nonnegative rate and time, the exponentially scaled spectral radius of a positive
definite qubit density operator is strictly less than one. -/
theorem exp_mul_spectrumRadius_lt_one (γ : ℝ) (hγ : 0 ≤ γ) (u : ℝ) (hu : 0 ≤ u)
    {τ : Operator 2} (hτ : IsDensityOperator τ) (hτfull : τ.PosDef) :
    Real.exp (-(γ * u)) * spectrumRadius τ < 1 := by
  have hθ1 : Real.exp (-(γ * u)) ≤ 1 := by
    have h := Real.exp_le_exp.mpr (show -(γ * u) ≤ 0 by nlinarith)
    simpa using! h
  calc
    Real.exp (-(γ * u)) * spectrumRadius τ ≤ 1 * spectrumRadius τ :=
      mul_le_mul_of_nonneg_right hθ1 (spectrumRadius_nonneg τ)
    _ = spectrumRadius τ := one_mul _
    _ < 1 := spectrumRadius_lt_one hτ hτfull

/-- Computes the time derivative of relative entropy along the depolarizing orbit of a positive
definite qubit density operator. -/
theorem hasDerivAt_depolarizing_relativeEntropy (γ : ℝ) (hγ : 0 ≤ γ)
    {τ : Operator 2} (hτ : IsDensityOperator τ) (hτfull : τ.PosDef)
    (u : ℝ) (hu : 0 ≤ u) :
    HasDerivAt
      (fun v : ℝ => relativeEntropy (lindbladSemigroup (depolarizingGKSL γ) v τ)
        maximallyMixed)
      (-γ * ((Real.exp (-(γ * u)) * spectrumRadius τ) / 2 *
        Real.log ((1 + Real.exp (-(γ * u)) * spectrumRadius τ) /
          (1 - Real.exp (-(γ * u)) * spectrumRadius τ)))) u := by
  have hx0 := exp_mul_spectrumRadius_nonneg γ u τ
  have hx1 := exp_mul_spectrumRadius_lt_one γ hγ u hu hτ hτfull
  have hxm1 : -1 < Real.exp (-(γ * u)) * spectrumRadius τ := by linarith
  have hfun : (fun v : ℝ => relativeEntropy
      (lindbladSemigroup (depolarizingGKSL γ) v τ) maximallyMixed) =
      (fun v : ℝ => twoLevelMix (Real.exp (-(γ * v)) * spectrumRadius τ)) := by
    funext v
    exact relativeEntropy_depolarizing_orbit γ hγ v hτ.1.1 hτ.2
  rw [hfun]
  have hlin : HasDerivAt (fun v : ℝ => -(γ * v)) (-γ) u := by
    simpa only [id_eq, mul_one] using! ((hasDerivAt_id u).const_mul γ).neg
  have hexp : HasDerivAt (fun v : ℝ => Real.exp (-(γ * v)))
      (Real.exp (-(γ * u)) * (-γ)) u := by
    simpa only [Function.comp_apply] using!
      (Real.hasDerivAt_exp (-(γ * u))).comp u hlin
  have hmul := hexp.mul_const (spectrumRadius τ)
  have hcomp := (hasDerivAt_twoLevelMix hxm1 hx1).comp u hmul
  convert! hcomp using 1; ring

/-- A positive depolarizing rate satisfies `EntropyProductionIneq` relative to the maximally
mixed state with that rate constant. -/
theorem depolarizing_entropyProduction (γ : ℝ) (hγ : 0 < γ) :
    EntropyProductionIneq (depolarizingGKSL γ) maximallyMixed γ := by
  refine ⟨hγ, ?_⟩
  intro τ hτ hτfull u hu
  let θ := Real.exp (-(γ * u))
  let s := spectrumRadius τ
  have hx0 : 0 ≤ θ * s := exp_mul_spectrumRadius_nonneg γ u τ
  have hx1 : θ * s < 1 := exp_mul_spectrumRadius_lt_one γ hγ.le u hu hτ hτfull
  refine ⟨-γ * ((θ * s) / 2 * Real.log ((1 + θ * s) / (1 - θ * s))), ?_, ?_⟩
  · simpa [θ, s] using!
      hasDerivAt_depolarizing_relativeEntropy γ hγ.le hτ hτfull u hu
  · rw [relativeEntropy_depolarizing_orbit γ hγ.le u hτ.1.1 hτ.2]
    change -γ * ((θ * s) / 2 * Real.log ((1 + θ * s) / (1 - θ * s))) ≤
      -2 * γ * twoLevelMix (θ * s)
    have hep := twoLevelMix_entropyProduction hx0 hx1
    have hmul := mul_le_mul_of_nonneg_left hep hγ.le
    nlinarith

/-- For positive definite qubit states and nonnegative time, proves exponential relative-entropy
decay at twice the depolarizing rate and the corresponding trace-distance bound. -/
theorem frontier1 (γ : ℝ) (hγ : 0 < γ) {σ : Operator 2}
    (hσ : IsDensityOperator σ) (hσfull : σ.PosDef) (t : ℝ) (ht : 0 ≤ t) :
    relativeEntropy (lindbladSemigroup (depolarizingGKSL γ) t σ) maximallyMixed
      ≤ Real.exp (-2 * γ * t) * relativeEntropy σ maximallyMixed
      ∧ traceDistance (lindbladSemigroup (depolarizingGKSL γ) t σ) maximallyMixed
        ≤ Real.exp (-γ * t) * Real.sqrt (2 * relativeEntropy σ maximallyMixed) := by
  refine Qatlib.Concepts.QuantumGibbs.FormAlgebra.LindbladSemigroup.frontier1
    (depolarizingGKSL γ) hσ hσfull (depolarizing_entropyProduction γ hγ)
    (by norm_num : (0 : ℝ) ≤ 2) ?_ ?_ t ht
  · exact mul_nonneg (by norm_num) (relativeEntropy_maximallyMixed_nonneg hσ)
  · intro τ hτ
    exact traceDistance_le_sqrt_two_relativeEntropy hτ

end Qatlib.Concepts.QuantumGibbs.FormAlgebra.DepolarizingEntropySpectrum
