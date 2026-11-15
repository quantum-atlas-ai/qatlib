/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Qatlib.Concepts.OrderedOracle.TiSdpBridge.ApproximationAlgorithmsDefs
public import Qatlib.Concepts.SignalPrimitive.PhaseFrontend.SignPolynomial
public import Qatlib.Concepts.QsvtCore.LinearSystems.NearOptimalReciprocal
public import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.MarkovBrothers
public import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Optimization
public import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.HermitianFunctionStability
public import Qatlib.Concepts.SketchSpectral.MatrixFunctions.HermitianRankLogStability
public import Qatlib.Concepts.QsvtCore.LinearSystems.WindowedReciprocal

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.OrderedOracle.TiSdpBridge Qatlib.Concepts.WalshMoment.Forrelation Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.OrderedOracle.TiSdpBridge

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.LchsSimulation.Quadrature
open Qatlib.Concepts.SketchSpectral.MatrixFunctions
open Qatlib.Concepts.QsvtCore.LinearSystems

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge

open Matrix Qatlib.Concepts.OrderedOracle.TiSdpBridge
open scoped Classical Matrix.Norms.L2Operator

private def NonNormalResolventClass {D : ℕ} (A : Operator D) (Λ : Fin D → ℂ)
    (V : Operator D) (κ : ℝ) (zs : Finset ℂ) (r : ℝ) : Prop :=
  V.det ≠ 0 ∧ ‖V‖ * ‖V⁻¹‖ ≤ κ ∧
    (∀ i : Fin D, ∀ z ∈ zs, r ≤ ‖Λ i - z‖) ∧
    (∀ z ∈ zs, ResolventCertificate A z r)

private noncomputable def nonNormalCalculus {D : ℕ} (V : Operator D) (Λ : Fin D → ℂ)
    (f : ℂ → ℂ) : Operator D :=
  V * Matrix.diagonal (fun i => f (Λ i)) * V⁻¹

/-- An entrywise bound on a square matrix bounds its Schur multiplier by the dimension times
that bound. -/
theorem schurMultiplierBounded_of_entry_le {D : ℕ} (B : Operator D) (c : ℝ)
    (hc : 0 ≤ c) (hB : ∀ i j, ‖B i j‖ ≤ c) :
    SchurMultiplierBounded B ((D : ℝ) * c) := by
  intro X Y
  let M := X - Y
  have he (i j : Fin D) : ‖(B ⊙ M) i j‖ ≤ c * ‖M‖ := by
    change ‖B i j * M i j‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (hB i j) (gamma2_operator_entry_bound M i j)
      (norm_nonneg _) hc
  have hsq : spectralFrobenius (B ⊙ M) ^ 2 ≤ ((D : ℝ) * c * ‖M‖) ^ 2 := by
    rw [spectralFrobenius_sq]
    calc
      (∑ i, ∑ j, Complex.normSq ((B ⊙ M) i j))
          ≤ ∑ _i : Fin D, ∑ _j : Fin D, (c * ‖M‖) ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            apply Finset.sum_le_sum
            intro j _
            rw [Complex.normSq_eq_norm_sq]
            exact pow_le_pow_left₀ (norm_nonneg _) (he i j) 2
      _ = ((D : ℝ) * c * ‖M‖) ^ 2 := by simp; ring
  have hF : spectralFrobenius (B ⊙ M) ≤ (D : ℝ) * c * ‖M‖ := by
    have hn : 0 ≤ (D : ℝ) * c * ‖M‖ := by positivity
    nlinarith [spectralFrobenius_nonneg (B ⊙ M)]
  exact (spectral_operator_norm_le_frobenius (B ⊙ M)).trans hF

/-- Establishes the Schur multiplier bridge `schurMultiplierBridge`. -/
theorem clause55_schurMultiplierBridge : schurMultiplierBridge := by
  intro D A z r hcert B hB
  have h := schurMultiplierBounded_of_entry_le B (1 / r) (by positivity [hcert.1]) hB
  simpa only [div_eq_mul_inv, one_mul] using! h

/-- Establishes the Chebyshev recursion identity used by clause one. -/
private theorem clause1_chebRecursion : Qatlib.Concepts.OrderedOracle.TiSdpBridge.chebRecursionIdentity := by
  intro n
  exact Polynomial.Chebyshev.T_add_two ℝ (n : ℤ)

/-- Establishes the cosine representation of the Chebyshev polynomials. -/
private theorem clause1_chebTriangle : Qatlib.Concepts.OrderedOracle.TiSdpBridge.chebTriangleRepresentation :=
  fun _ _ => Polynomial.Chebyshev.T_real_cos _ _

/-- The integral of the cosine of a nonzero integer multiple over zero to pi vanishes. -/
private theorem cosIntegralIntMul (z : ℤ) (hz : ((z : ℝ)) ≠ 0) :
    ∫ x in (0 : ℝ)..Real.pi, Real.cos ((z : ℝ) * x) = 0 := by
  have hder : ∀ x : ℝ,
      HasDerivAt (fun t => Real.sin ((z : ℝ) * t) / (z : ℝ)) (Real.cos ((z : ℝ) * x)) x := by
    intro x
    have h3 := (((hasDerivAt_id x).const_mul (z : ℝ)).sin).div_const (z : ℝ)
    simp only [id_eq] at h3
    rw [show Real.cos ((z : ℝ) * x) * ((z : ℝ) * 1) / (z : ℝ) = Real.cos ((z : ℝ) * x) from by
      field_simp] at h3
    exact h3
  have hint : IntervalIntegrable (fun x => Real.cos ((z : ℝ) * x)) MeasureTheory.volume
      (0 : ℝ) Real.pi :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hder x) hint]
  simp [Real.sin_int_mul_pi]

/-- Establishes the Chebyshev orthogonality property used by clause one. -/
private theorem clause1_chebOrthogonality : Qatlib.Concepts.OrderedOracle.TiSdpBridge.chebOrthogonality := by
  intro m n hmn
  have hint1 : IntervalIntegrable
      (fun x : ℝ => Real.cos ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * x)) MeasureTheory.volume
      (0 : ℝ) Real.pi :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable
      (fun x : ℝ => Real.cos ((((m : ℤ) + (n : ℤ) : ℤ) : ℝ) * x)) MeasureTheory.volume
      (0 : ℝ) Real.pi :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have z1 : ∫ x in (0 : ℝ)..Real.pi,
      Real.cos ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * x) = 0 := by
    refine cosIntegralIntMul _ ?_
    rw [Int.cast_ne_zero]
    omega
  have z2 : ∫ x in (0 : ℝ)..Real.pi,
      Real.cos ((((m : ℤ) + (n : ℤ) : ℤ) : ℝ) * x) = 0 := by
    refine cosIntegralIntMul _ ?_
    rw [Int.cast_ne_zero]
    omega
  have hfun : ∀ x : ℝ, (1 / 2 : ℝ) * (Real.cos ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * x) +
      Real.cos ((((m : ℤ) + (n : ℤ) : ℤ) : ℝ) * x)) =
      Real.cos ((m : ℝ) * x) * Real.cos ((n : ℝ) * x) := by
    intro x
    have h := Real.two_mul_cos_mul_cos ((m : ℝ) * x) ((n : ℝ) * x)
    have e1 : ((m : ℝ) * x - (n : ℝ) * x) = ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * x) := by
      push_cast
      ring
    have e2 : ((m : ℝ) * x + (n : ℝ) * x) = ((((m : ℤ) + (n : ℤ) : ℤ) : ℝ) * x) := by
      push_cast
      ring
    rw [e1, e2] at h
    linarith
  rw [intervalIntegral.integral_congr (fun x _ => (hfun x).symm),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add hint1 hint2, z1, z2]
  ring

/-- Establishes the Chebyshev node value property used by clause one. -/
private theorem clause1_chebNodeValues : Qatlib.Concepts.OrderedOracle.TiSdpBridge.chebNodeValues := by
  intro N j _hj n
  unfold Qatlib.Concepts.OrderedOracle.TiSdpBridge.chebNode
  rw [clause1_chebTriangle n]
  congr 1
  ring

/-- Establishes the Gauss-Legendre comparison property. -/
private theorem clause1_gaussComparison : Qatlib.Concepts.OrderedOracle.TiSdpBridge.gaussLegendreComparison := by
  intro Q hQ
  obtain ⟨node, weight, _h1, _h2, _h3, hexact, hclosed⟩ := gauss_legendre_rule_exists Q hQ
  exact ⟨node, weight, gauss_rule_weight_sum Q node weight hexact, hexact, hclosed⟩

/-- Establishes the cellwise Gauss-Legendre comparison property. -/
private theorem clause1_gaussCellComparison : Qatlib.Concepts.OrderedOracle.TiSdpBridge.gaussLegendreCellComparison :=
  fun Q hQ a h node weight f hpos hex homega hcd =>
    gauss_legendre_cell_error_bound Q a h node weight f hQ hpos hex homega hcd

/-- Scalar approximation bounds transfer to odd singular transforms. -/
private theorem clause1_scalarBridge : Qatlib.Concepts.OrderedOracle.TiSdpBridge.scalarToSingularBridge :=
  fun _ _ _ _ _ _ A f g _ε hε hfg =>
    Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform_error_le A f g hε hfg

/-- Establishes the polynomial-to-singular-transform bridge. -/
private theorem clause1_polyBridge : Qatlib.Concepts.OrderedOracle.TiSdpBridge.polynomialToSingularBridge := by
  intro O I _ _ _ _ A p q ε hε hpq
  refine clause1_scalarBridge O I A (fun x => ((p.eval x : ℝ) : ℂ))
    (fun x => ((q.eval x : ℝ) : ℂ)) ε hε (fun i => ?_)
  rw [← Complex.ofReal_sub, Complex.norm_real]
  exact hpq i

/-- A polynomial bounded on the unit interval has the stated degree-squared derivative bound
there. -/
private theorem clause1_markovBinding :
    ∀ (d : ℕ) (g : Polynomial ℝ), g.natDegree ≤ d → ∀ C : ℝ, 0 ≤ C →
        (∀ x ∈ Set.Icc (-1 : ℝ) 1, |g.eval x| ≤ C) →
          ∀ x ∈ Set.Icc (-1 : ℝ) 1, |g.derivative.eval x| ≤ 2 * (d : ℝ) ^ 2 * C :=
  fun _ _g hd _ hC hb => markov_brothers_deriv_le hd hC hb

/-- The sign polynomial satisfies its stated error bound away from zero within the unit
interval. -/
private theorem clause1_signBinding :
    ∀ (k : ℕ) (δ x : ℝ), 0 < δ → δ ≤ |x| → |x| ≤ 1 →
        |Real.sign x - (Qatlib.Concepts.SignalPrimitive.PhaseFrontend.signPolynomial k).eval x| ≤
          Qatlib.Concepts.SignalPrimitive.PhaseFrontend.signPolynomialError δ k :=
  fun k _δ _x hδ hgap hx => Qatlib.Concepts.SignalPrimitive.PhaseFrontend.signPolynomial_error_le k hδ hgap hx

/-- The near-optimal reciprocal polynomial approximates inversion with error at most twice the
tolerance on the admissible absolute-value interval. -/
private theorem clause1_reciprocalBinding :
    ∀ (κ ε x : ℝ), 1 < κ → 0 < ε → ε ≤ 1 / 2 → |x| ∈ Set.Icc κ⁻¹ 1 →
        |(nearOptimalReciprocalPolynomial κ ε).eval x - x⁻¹| ≤ 2 * ε :=
  fun κ ε x hκ hε hε1 hx => nearOptimalReciprocal_error_of_abs κ ε hκ hε hε1 x hx

/-- A bounded odd windowed reciprocal polynomial exists with the stated degree, parity, and
approximation budgets. -/
private theorem clause1_windowBinding :
    ∀ (ε δ : ℝ), 0 < ε → ε ≤ δ → δ ≤ 1 / 2 →
        ∃ (Pw : Polynomial ℝ) (J k : ℕ),
          (2 * J + 1 : ℝ) ≤ 32 * (2 / δ) * Real.log (16 / (δ * ε)) ∧
            ((3 : ℝ) ^ k) ≤ 3 * (64 / (δ * ε)) ^ (12 / (δ * δ)) ∧
            Pw.natDegree ≤ 2 * J + 1 + 2 * 3 ^ k ∧
            Qatlib.Concepts.QspSimulation.Achievability.HasRealParity (2 * J + 1 + 2 * 3 ^ k) Pw ∧
            (∀ x ∈ Set.Icc (-1 : ℝ) 1, |Pw.eval x| ≤ 1) ∧
            Pw.eval 0 = 0 ∧
            (∀ x ∈ Set.Icc δ 1, |Pw.eval x - (δ / 2) / x| ≤ ε) :=
  windowed_reciprocal_exists

/-- The near-optimal reciprocal polynomial gives the stated error bound for odd singular
transforms under the singular-value gap assumption. -/
private theorem clause1_reciprocalBridgeApplied :
    ∀ (O I : Type) [Fintype O] [Fintype I] [DecidableEq O] [DecidableEq I]
        (A : Matrix O I ℂ) (κ ε : ℝ),
      1 < κ → 0 < ε → ε ≤ 1 / 2 →
        (∀ i : Fin (Fintype.card I),
            |Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i| ∈ Set.Icc κ⁻¹ 1) →
        ‖Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A
              (fun x => (((nearOptimalReciprocalPolynomial κ ε).eval x : ℝ) : ℂ)) -
            Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A (fun x => ((x⁻¹ : ℝ) : ℂ))‖ ≤
          2 * ε := by
  intro O I _ _ _ _ A κ ε hκ hε hε1 hsv
  refine clause1_scalarBridge O I A (fun x => (((nearOptimalReciprocalPolynomial κ ε).eval x : ℝ) : ℂ))
    (fun x => ((x⁻¹ : ℝ) : ℂ)) (2 * ε) (by positivity) (fun i => ?_)
  have h := nearOptimalReciprocal_error_of_abs κ ε hκ hε hε1 _ (hsv i)
  rw [← Complex.ofReal_sub, Complex.norm_real]
  exact h

/-- A bounded windowed reciprocal polynomial gives the stated odd singular-transform
approximation and degree budgets. -/
private theorem clause1_windowBridgeApplied :
    ∀ (O I : Type) [Fintype O] [Fintype I] [DecidableEq O] [DecidableEq I]
        (A : Matrix O I ℂ) (ε δ : ℝ),
      0 < ε → ε ≤ δ → δ ≤ 1 / 2 →
        (∀ i : Fin (Fintype.card I),
            Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i ∈ Set.Icc δ 1) →
        ∃ (Pw : Polynomial ℝ) (J k : ℕ),
          (2 * J + 1 : ℝ) ≤ 32 * (2 / δ) * Real.log (16 / (δ * ε)) ∧
            ((3 : ℝ) ^ k) ≤ 3 * (64 / (δ * ε)) ^ (12 / (δ * δ)) ∧
            Pw.natDegree ≤ 2 * J + 1 + 2 * 3 ^ k ∧
            (∀ x ∈ Set.Icc (-1 : ℝ) 1, |Pw.eval x| ≤ 1) ∧
            ‖Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A (fun x => ((Pw.eval x : ℝ) : ℂ)) -
                Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A
                  (fun x => (((δ / 2) / x : ℝ) : ℂ))‖ ≤ ε := by
  intro O I _ _ _ _ A ε δ hε hεδ hδ2 hsv
  obtain ⟨Pw, J, k, hJ, hk, hdeg, _hpar, hbnd, _h0, happrox⟩ :=
    windowed_reciprocal_exists ε δ hε hεδ hδ2
  refine ⟨Pw, J, k, hJ, hk, hdeg, hbnd, ?_⟩
  refine clause1_scalarBridge O I A (fun x => ((Pw.eval x : ℝ) : ℂ))
    (fun x => (((δ / 2) / x : ℝ) : ℂ)) ε hε.le (fun i => ?_)
  have h := happrox (Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i) (hsv i)
  rw [← Complex.ofReal_sub, Complex.norm_real]
  exact h

/-- With a positive gap at most one, the sign polynomial odd singular transform satisfies
`signPolynomialError`. -/
theorem signPolynomial_singular_error_le
    (O I : Type) [Fintype O] [Fintype I] [DecidableEq O] [DecidableEq I]
    (A : Matrix O I ℂ) (k : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsv : ∀ i : Fin (Fintype.card I),
      δ ≤ |Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i| ∧
        |Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i| ≤ 1) :
    ‖Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A
        (fun x => (((Qatlib.Concepts.SignalPrimitive.PhaseFrontend.signPolynomial k).eval x : ℝ) : ℂ)) -
      Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A (fun x => ((Real.sign x : ℝ) : ℂ))‖ ≤
      Qatlib.Concepts.SignalPrimitive.PhaseFrontend.signPolynomialError δ k := by
  have herr : 0 ≤ Qatlib.Concepts.SignalPrimitive.PhaseFrontend.signPolynomialError δ k := by
    unfold Qatlib.Concepts.SignalPrimitive.PhaseFrontend.signPolynomialError
    exact pow_nonneg (by nlinarith) _
  apply clause1_scalarBridge O I A _ _ _ herr
  intro i
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  exact Qatlib.Concepts.SignalPrimitive.PhaseFrontend.signPolynomial_error_le k hδ (hsv i).1
      (hsv i).2

/-- Collects the clause-one approximation bridges and polynomial bounds with an admissible sign
gap. -/
theorem clause1_with_admissible_sign_gap :
  Qatlib.Concepts.OrderedOracle.TiSdpBridge.chebRecursionIdentity ∧
    Qatlib.Concepts.OrderedOracle.TiSdpBridge.chebTriangleRepresentation ∧
    Qatlib.Concepts.OrderedOracle.TiSdpBridge.chebOrthogonality ∧
    Qatlib.Concepts.OrderedOracle.TiSdpBridge.chebNodeValues ∧
    Qatlib.Concepts.OrderedOracle.TiSdpBridge.gaussLegendreComparison ∧
    Qatlib.Concepts.OrderedOracle.TiSdpBridge.gaussLegendreCellComparison ∧
    Qatlib.Concepts.OrderedOracle.TiSdpBridge.scalarToSingularBridge ∧
    Qatlib.Concepts.OrderedOracle.TiSdpBridge.polynomialToSingularBridge ∧

    (∀ (d : ℕ) (g : Polynomial ℝ), g.natDegree ≤ d → ∀ C : ℝ, 0 ≤ C →
        (∀ x ∈ Set.Icc (-1 : ℝ) 1, |g.eval x| ≤ C) →
          ∀ x ∈ Set.Icc (-1 : ℝ) 1, |g.derivative.eval x| ≤ 2 * (d : ℝ) ^ 2 * C) ∧

    (∀ (k : ℕ) (δ x : ℝ), 0 < δ → δ ≤ |x| → |x| ≤ 1 →
        |Real.sign x - (Qatlib.Concepts.SignalPrimitive.PhaseFrontend.signPolynomial k).eval x| ≤
          Qatlib.Concepts.SignalPrimitive.PhaseFrontend.signPolynomialError δ k) ∧

    (∀ (κ ε x : ℝ), 1 < κ → 0 < ε → ε ≤ 1 / 2 → |x| ∈ Set.Icc κ⁻¹ 1 →
        |(nearOptimalReciprocalPolynomial κ ε).eval x - x⁻¹| ≤ 2 * ε) ∧

    (∀ (ε δ : ℝ), 0 < ε → ε ≤ δ → δ ≤ 1 / 2 →
        ∃ (Pw : Polynomial ℝ) (J k : ℕ),
          (2 * J + 1 : ℝ) ≤ 32 * (2 / δ) * Real.log (16 / (δ * ε)) ∧
            ((3 : ℝ) ^ k) ≤ 3 * (64 / (δ * ε)) ^ (12 / (δ * δ)) ∧
            Pw.natDegree ≤ 2 * J + 1 + 2 * 3 ^ k ∧
            Qatlib.Concepts.QspSimulation.Achievability.HasRealParity (2 * J + 1 + 2 * 3 ^ k) Pw ∧
            (∀ x ∈ Set.Icc (-1 : ℝ) 1, |Pw.eval x| ≤ 1) ∧
            Pw.eval 0 = 0 ∧
            (∀ x ∈ Set.Icc δ 1, |Pw.eval x - (δ / 2) / x| ≤ ε)) ∧

    (∀ (O I : Type) [Fintype O] [Fintype I] [DecidableEq O] [DecidableEq I]
        (A : Matrix O I ℂ) (κ ε : ℝ),
      1 < κ → 0 < ε → ε ≤ 1 / 2 →
        (∀ i : Fin (Fintype.card I),
            |Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i| ∈ Set.Icc κ⁻¹ 1) →
        ‖Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A
              (fun x => (((nearOptimalReciprocalPolynomial κ ε).eval x : ℝ) : ℂ)) -
            Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A (fun x => ((x⁻¹ : ℝ) : ℂ))‖ ≤
          2 * ε) ∧

    (∀ (O I : Type) [Fintype O] [Fintype I] [DecidableEq O] [DecidableEq I]
        (A : Matrix O I ℂ) (k : ℕ) (δ : ℝ),
      0 < δ → δ ≤ 1 →
        (∀ i : Fin (Fintype.card I),
            δ ≤ |Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i| ∧
              |Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i| ≤ 1) →
        ‖Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A
              (fun x => (((Qatlib.Concepts.SignalPrimitive.PhaseFrontend.signPolynomial k).eval x : ℝ) : ℂ)) -
            Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A (fun x => ((Real.sign x : ℝ) : ℂ))‖ ≤
          Qatlib.Concepts.SignalPrimitive.PhaseFrontend.signPolynomialError δ k) ∧

    (∀ (O I : Type) [Fintype O] [Fintype I] [DecidableEq O] [DecidableEq I]
        (A : Matrix O I ℂ) (ε δ : ℝ),
      0 < ε → ε ≤ δ → δ ≤ 1 / 2 →
        (∀ i : Fin (Fintype.card I),
            Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i ∈ Set.Icc δ 1) →
        ∃ (Pw : Polynomial ℝ) (J k : ℕ),
          (2 * J + 1 : ℝ) ≤ 32 * (2 / δ) * Real.log (16 / (δ * ε)) ∧
            ((3 : ℝ) ^ k) ≤ 3 * (64 / (δ * ε)) ^ (12 / (δ * δ)) ∧
            Pw.natDegree ≤ 2 * J + 1 + 2 * 3 ^ k ∧
            (∀ x ∈ Set.Icc (-1 : ℝ) 1, |Pw.eval x| ≤ 1) ∧
            ‖Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A (fun x => ((Pw.eval x : ℝ) : ℂ)) -
                Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A
                  (fun x => (((δ / 2) / x : ℝ) : ℂ))‖ ≤ ε) := by
  exact ⟨clause1_chebRecursion, clause1_chebTriangle, clause1_chebOrthogonality, clause1_chebNodeValues,
    clause1_gaussComparison, clause1_gaussCellComparison, clause1_scalarBridge, clause1_polyBridge,
    clause1_markovBinding, clause1_signBinding, clause1_reciprocalBinding, clause1_windowBinding,
    clause1_reciprocalBridgeApplied, signPolynomial_singular_error_le, clause1_windowBridgeApplied⟩

/-- A scalar Lipschitz bound on the paired spectra gives Frobenius stability of Hermitian
functional calculus. -/
private theorem clause55_frobeniusEndpoint :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A B : Matrix I I ℂ)
        (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℂ) (L : ℝ),
      0 ≤ L →
        (∀ i j : Fin (Fintype.card I),
            ‖f (orderedHermitianValues hA i) - f (orderedHermitianValues hB j)‖ ≤
              L * |orderedHermitianValues hA i - orderedHermitianValues hB j|) →
        spectralFrobenius (hermitianFunction A hA f - hermitianFunction B hB f) ≤
          L * spectralFrobenius (A - B) :=
  hermitian_spectral_function_frobenius_stability

/-- A rank-dependent quasicommutator bound transfers to a functional-calculus difference bound
using the smaller matrix rank. -/
private theorem clause55_minRankTransfer :
    ∀ c₀ : ℝ,
      (∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (hA : A.IsHermitian)
          (B : Matrix I I ℂ) (hB : B.IsHermitian) (S : Matrix I I ℂ) (f : ℝ → ℂ)
          (L : ℝ),
        0 ≤ L → hermitianPairScalarLipschitz A hA B hB f L →
          ‖hermitianFunction A hA f * S - S * hermitianFunction B hB f‖ ≤
            c₀ * hermitianRankLogWeight A.rank * L * ‖A * S - S * B‖) →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (A B : Matrix I I ℂ)
          (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℂ) (L : ℝ),
        0 ≤ L → hermitianPairScalarLipschitz A hA B hB f L →
        ‖hermitianFunction A hA f - hermitianFunction B hB f‖ ≤
          c₀ * hermitianRankLogWeight (min A.rank B.rank) * L * ‖A - B‖ :=
  fun c₀ hq => hermitianFunction_min_rank_stability_of_quasicommutator_bound c₀ hq

/-- The stated rank-weighted functional-calculus stability bound holds when the smaller rank is
zero. -/
private theorem clause55_minRankZero :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A B : Matrix I I ℂ)
        (hA : A.IsHermitian) (hB : B.IsHermitian) (_hr : min A.rank B.rank = 0)
        (f : ℝ → ℂ) (L : ℝ),
      0 ≤ L → hermitianPairScalarLipschitz A hA B hB f L →
      ‖hermitianFunction A hA f - hermitianFunction B hB f‖ ≤
        hermitianRankLogWeight (min A.rank B.rank) * L * ‖A - B‖ := by
  intro I _ _ A B hA hB hr f L hL hf
  exact hermitianFunction_operator_stability_min_rank_zero A B hA hB hr f L hL hf

/-- Scalar approximation on the eigenvalues of a nonnormal resolvent-class matrix transfers with
the stated condition factor. -/
private theorem clause55_nonNormalTransport :
    ∀ (D : ℕ) (A : Operator D) (Λ : Fin D → ℂ) (V : Operator D) (κ : ℝ)
        (zs : Finset ℂ) (r : ℝ) (f : ℂ → ℂ) (p : Polynomial ℂ) (ε : ℝ),
      NonNormalResolventClass A Λ V κ zs r → 0 ≤ ε →
        (∀ i, ‖f (Λ i) - p.eval (Λ i)‖ ≤ ε) →
        ‖nonNormalCalculus V Λ f - nonNormalCalculus V Λ (fun z => p.eval z)‖ ≤ κ * ε := by
  intro D A Λ V κ zs r f p ε hcl hε hpt
  obtain ⟨_hdet, hκ, _sep, _res⟩ := hcl
  have hdiag : nonNormalCalculus V Λ f - nonNormalCalculus V Λ (fun z => p.eval z) =
      V * Matrix.diagonal (fun i => f (Λ i) - p.eval (Λ i)) * V⁻¹ := by
    unfold nonNormalCalculus
    rw [← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]
  have hnorm : ‖Matrix.diagonal (fun i => f (Λ i) - p.eval (Λ i))‖ ≤ ε := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hε).2 hpt
  have hl : ‖V * Matrix.diagonal (fun i => f (Λ i) - p.eval (Λ i))‖ ≤ ‖V‖ * ε :=
    (Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul (le_refl _) hnorm (norm_nonneg _) (norm_nonneg _))
  rw [hdiag]
  exact (Matrix.l2_opNorm_mul _ _).trans
    ((mul_le_mul hl (le_refl _) (norm_nonneg _) (by positivity)).trans
      ((mul_right_comm ‖V‖ ε ‖V⁻¹‖).trans_le (mul_le_mul_of_nonneg_right hκ hε)))

/-- The proposed universal sign-transform error bound fails without an upper bound on the gap
parameter. -/
theorem clause1_signBridgeApplication_false :
    ¬ (∀ (O I : Type) [Fintype O] [Fintype I] [DecidableEq O] [DecidableEq I]
        (A : Matrix O I ℂ) (k : ℕ) (δ : ℝ),
      0 < δ →
        (∀ i : Fin (Fintype.card I),
            δ ≤ |Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i| ∧
              |Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i| ≤ 1) →
        ‖Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A
              (fun x => (((Qatlib.Concepts.SignalPrimitive.PhaseFrontend.signPolynomial k).eval x : ℝ) : ℂ)) -
            Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A (fun x => ((Real.sign x : ℝ) : ℂ))‖ ≤
          Qatlib.Concepts.SignalPrimitive.PhaseFrontend.signPolynomialError δ k) := by
  intro h
  have h0 := h (O := Fin 1) (I := Fin 0) (A := fun _ _ => (0 : ℂ)) (k := 0) (δ := 2)
    (by norm_num)
    (by intro i; exact absurd i.2 (by simp))
  simp only [Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform] at h0
  rw [show Qatlib.Concepts.SignalPrimitive.PhaseFrontend.signPolynomialError 2 0 = -3 from by
    norm_num [Qatlib.Concepts.SignalPrimitive.PhaseFrontend.signPolynomialError]] at h0
  norm_num at h0

/-- The two-dimensional scalar diagonal matrix with value square root of two is Hermitian. -/
private theorem herm2 :
    (Matrix.diagonal (fun _ : Fin 2 => (Real.sqrt 2 : ℂ))).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  split_ifs <;> simp_all

/-- Every diagonal value in the stated orthonormal spectral representation of the
square-root-of-two scalar matrix equals square root of two. -/
private theorem lam_eq {U : Matrix (Fin 2) (Fin 2) ℂ} {lam : Fin 2 → ℝ}
    (hu : Uᴴ * U = 1)
    (hAeq : (Matrix.diagonal (fun _ : Fin 2 => (Real.sqrt 2 : ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) =
      U * Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ)) * Uᴴ) : ∀ i, lam i = Real.sqrt 2 := by
  have hsmul : (Matrix.diagonal (fun _ : Fin 2 => (Real.sqrt 2 : ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) =
      (Real.sqrt 2 : ℂ) • 1 := by
    ext a b
    simp [Matrix.diagonal, Matrix.one_apply]
  have h2 : Uᴴ * (Matrix.diagonal (fun _ : Fin 2 => (Real.sqrt 2 : ℂ)) :
      Matrix (Fin 2) (Fin 2) ℂ) * U = Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ)) := by
    calc Uᴴ * (Matrix.diagonal (fun _ : Fin 2 => (Real.sqrt 2 : ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) * U
        = (Uᴴ * U) * Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ)) * (Uᴴ * U) := by
          rw [hAeq]; noncomm_ring
      _ = 1 * Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ)) * 1 := by rw [hu]
      _ = Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ)) := by simp
  intro i
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i i) h2
  rw [hsmul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Matrix.mul_one, hu] at h
  simp at h
  exact h.symm

/-- No spectral certificate satisfies the stated correctness predicate for the
square-root-of-two scalar matrix at positive tolerance. -/
private theorem no_cert {cert : SpectralCertificate 2} {ε : ℝ} (hε : 0 < ε)
    (hcorr : SpectralApproximationCorrect (Matrix.diagonal (fun _ => (Real.sqrt 2 : ℂ))) cert ε) :
    False := by
  obtain ⟨U, lam, hU, hAeq, hin, hord, _hg, _hm, _hbt, _hbs⟩ := hcorr herm2 hε
  have hlam := lam_eq (Matrix.mem_unitaryGroup_iff'.mp hU) hAeq
  have e0 := hin 0
  have e1 := hin 1
  have e01 : ((cert.values 0).2 : ℝ) ≤ ((cert.values 1).1 : ℝ) := by
    exact_mod_cast hord 0 1 (by decide)
  rw [hlam 0] at e0
  rw [hlam 1] at e1
  have hq : ((cert.values 0).2 : ℝ) = Real.sqrt 2 := le_antisymm (le_trans e01 e1.1) e0.2
  exact irrational_sqrt_two ⟨(cert.values 0).2, hq⟩

/-- The repeated square-root-of-two eigenvalue example admits no correct spectral certificate at
tolerance one. -/
theorem clause47_certificate_sqrt2_repeated_eigenvalue_false :
    ¬ (∃ cert : SpectralCertificate 2,
        SpectralApproximationCorrect (Matrix.diagonal (fun _ : Fin 2 => (Real.sqrt 2 : ℂ))) cert 1) := by
  rintro ⟨cert, hcorr⟩
  exact no_cert one_pos hcorr

/-- The square-root-of-two scalar matrix refutes the stated universal numerical
functional-calculus specification. -/
theorem clause55_functionalCalculusNumericSpec_sqrt2_false :
    let A : Operator 2 := Matrix.diagonal (fun _ : Fin 2 => (Real.sqrt 2 : ℂ))
    ¬ (∀ hA : A.IsHermitian,
        ∃ (cert : SpectralCertificate 2) (p : Polynomial ℝ) (B : Operator 2) (bt bs : ℕ),
          SpectralApproximationCorrect A cert 1 ∧
            (∀ x : ℝ, (∃ i : Fin 2,
                x ∈ Set.Icc ((cert.values i).1 : ℝ) ((cert.values i).2 : ℝ)) →
              ‖(0 : ℂ) - ((p.eval x : ℝ) : ℂ)‖ ≤ (1 : ℝ)) ∧
            ‖B - hermitianFunction A hA (fun _ => (0 : ℂ))‖ ≤ (1 : ℝ) ∧
            bt ≤ (2 + 1) ^ 4 * (Nat.ceil (1 / (1 : ℝ)) + 1) ∧
            bs ≤ (2 + 1) ^ 4 * (Nat.ceil (1 / (1 : ℝ)) + 1)) := by
  dsimp only
  intro h
  obtain ⟨cert, p, B, bt, bs, hcorr, _hap, _hout, _hbt, _hbs⟩ := h herm2
  exact no_cert one_pos hcorr

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
