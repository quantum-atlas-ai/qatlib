/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.PhaseFrontend.ComputedPhaseQSVT
import Qatlib.Concepts.QspSimulation.Achievability.CleanSignalSimulation
import Qatlib.Foundations.PureStateMath.BornBridge.RelabelOperatorNorm

/-!
# Hamiltonian simulation from computed phase packets

Rational Taylor coefficients and finite phase synthesis produce the cosine and sine phase
packets used by `computedSignalBody`. Explicit segment lengths, truncation indices, and dyadic
tolerances control the scalar approximation and its transfer to Hermitian matrices, combining
QSP simulation [LowChuang2017] with the truncated Taylor approach [BerryEtAl2015Taylor].

The compiled body has a scale-eight block encoding with explicit query and gate counts.
`computed_signal_same_clean_segment` bounds the state error of the amplified body on the encoded
input space, and `computedSignalWord` repeats this amplified segment.

## Main statements

* `computed_signal_synthesized_packets`: Both finite phase searches return valid packets with
  uniform real response bounds.
* `computed_signal_phase_packets_and_body`: The compiled segment is well formed and has explicit
  encoding error and resource counts.
* `computed_signal_same_clean_segment`: The amplified segment approximates the encoded
  Hamiltonian evolution.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.WalkSearch.Spectral

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace Qatlib.Concepts.QspSimulation.JacobiAnger
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open scoped Classical BigOperators Matrix.Norms.L2Operator
/-- The positive segment count max(1, ⌈2|t|⌉) for rational evolution time t. -/
def computedSignalSegments (t : ℚ) : ℕ := max 1 ⌈2*|t|⌉₊
/-- The Taylor cutoff 32(k + ⌈log₂ r⌉ + 16), where r is `computedSignalSegments t` and the
logarithm is computed by `Nat.clog`. -/
def computedSignalCutoff (t : ℚ) (k : ℕ) : ℕ := 32*(k+Nat.clog 2 (computedSignalSegments t)+16)
/-- The rational dyadic tolerance 2 raised to the negative `computedSignalCutoff t k`. -/
def computedSignalTolerance (t : ℚ) (k : ℕ) : ℚ := (1/2)^computedSignalCutoff t k
/-- The first n rational coefficients of one quarter of the cosine Taylor polynomial at time t,
with odd coefficients set to zero. -/
def computedCosCoefficients (t : ℚ) (n : ℕ) : List ℚ :=
  List.ofFn (fun j : Fin n => if j.val%2=0 then (-1:ℚ)^(j.val/2)*t^j.val/(4*(j.val.factorial:ℚ)) else 0)
/-- The first n rational coefficients of one quarter of the sine Taylor polynomial at time t,
with even coefficients set to zero. -/
def computedSinCoefficients (t : ℚ) (n : ℕ) : List ℚ :=
  List.ofFn (fun j : Fin n => if j.val%2=1 then (-1:ℚ)^((j.val-1)/2)*t^j.val/(4*(j.val.factorial:ℚ)) else 0)
/-- Compile the cosine and sine phase packets synthesized for a single time segment, returning
the empty word if either synthesis produces no packet. -/
noncomputable def computedSignalBody {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    (F : Matrix H I ℂ) (t : ℚ) (k : ℕ) : List (AdjointStep (Bool×(Bool×H))) :=
  let n := computedSignalCutoff t k
  let u := t/(computedSignalSegments t:ℚ)
  match (finitePhaseSynthesis (computedCosCoefficients u n) (2*n) (computedSignalTolerance t k)).value,
    (finitePhaseSynthesis (computedSinCoefficients u n) (2*n+1) (computedSignalTolerance t k)).value with
  | some c,some s => compileHamiltonian F (gaussianRatComplex c.base) (c.phases.map gaussianRatComplex)
      (gaussianRatComplex s.base) (s.phases.map gaussianRatComplex)
  | _,_ => []
/-- Concatenate `computedSignalSegments t` copies of the scale-eight amplified word built from
`computedSignalBody F t k`. -/
noncomputable def computedSignalWord {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    (F : Matrix H I ℂ) (t : ℚ) (k : ℕ) : List (AdjointStep (Bool×(Bool×(Bool×H)))) :=
  (List.replicate (computedSignalSegments t)
    (scaleEightAmplifyWord (hamiltonianFrame F) (computedSignalBody F t k))).flatten

/-- Decompose (−i)^j into (−1)^(j/2) times the remaining power (−i)^(j mod 2). -/
theorem computed_signal_minus_I_pow (j : ℕ) :
    (-Complex.I)^j = (-1:ℂ)^(j/2) * (-Complex.I)^(j%2) := by
  have hj : j = 2*(j/2)+j%2 := by omega
  conv_lhs => rw [hj]
  rw [pow_add, pow_mul]
  norm_num [Complex.I_sq]

/-- The rational cosine and sine coefficients equal one quarter of the real part and one quarter
of the negative imaginary part, respectively, of the exponential Taylor coefficient. -/
theorem computed_signal_trig_scalar_coefficients (t : ℚ) (j : ℕ) :
    ((if j%2=0 then (-1:ℚ)^(j/2)*t^j/(4*(j.factorial:ℚ)) else 0):ℝ) =
      (1/4) * (exponentialTaylorCoefficient (t:ℝ) j).re ∧
    ((if j%2=1 then (-1:ℚ)^((j-1)/2)*t^j/(4*(j.factorial:ℚ)) else 0):ℝ) =
      (1/4) * (-(exponentialTaylorCoefficient (t:ℝ) j).im) := by
  let a : ℝ := (-1:ℝ)^(j/2)*(t:ℝ)^j/(j.factorial:ℝ)
  have ha : (a:ℂ) = (-1:ℂ)^(j/2)*((t:ℝ):ℂ)^j/(j.factorial:ℂ) := by
    simp only [a, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_natCast]
  have hp := computed_signal_minus_I_pow j
  have hj : j%2=0 ∨ j%2=1 := by omega
  rcases hj with hj | hj
  · have he : exponentialTaylorCoefficient (t:ℝ) j = (a:ℂ) := by
      rw [exponentialTaylorCoefficient, mul_pow, hp, hj]
      simpa using! ha.symm
    have hre : (exponentialTaylorCoefficient (t:ℝ) j).re = a := by
      rw [he]; exact Complex.ofReal_re a
    have him : (exponentialTaylorCoefficient (t:ℝ) j).im = 0 := by
      rw [he]; exact Complex.ofReal_im a
    rw [hre,him]
    simp only [hj, if_pos, if_false, Nat.zero_ne_one, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast,
        neg_zero, mul_zero]
    constructor
    · dsimp [a]
      field_simp
    · trivial
  · have hje : (j-1)/2 = j/2 := by omega
    have he : exponentialTaylorCoefficient (t:ℝ) j = (-Complex.I)*(a:ℂ) := by
      rw [exponentialTaylorCoefficient, mul_pow, hp, hj, pow_one, ha]
      ring
    have hre : (exponentialTaylorCoefficient (t:ℝ) j).re = 0 := by rw [he]; simp
    have him : (exponentialTaylorCoefficient (t:ℝ) j).im = -a := by rw [he]; simp
    rw [hre,him]
    simp only [hj, hje, if_pos, if_false, Nat.one_ne_zero, Rat.cast_neg, Rat.cast_one,
        Rat.cast_natCast, neg_neg, mul_zero]
    constructor
    · trivial
    · dsimp [a]
      field_simp

/-- The two rational coefficient lists represent `hamiltonianCosine` and `hamiltonianSine` under
`realTarget`, and each list has length n. -/
theorem computed_signal_native_trig_coefficients : ∀ (t : ℚ) (n : ℕ),
    realTarget (computedCosCoefficients t n) = hamiltonianCosine (t:ℝ) n ∧
    realTarget (computedSinCoefficients t n) = hamiltonianSine (t:ℝ) n ∧
    (computedCosCoefficients t n).length = n ∧ (computedSinCoefficients t n).length = n := by
  intro t n
  refine ⟨?_,?_,by simp [computedCosCoefficients],by simp [computedSinCoefficients]⟩
  · ext j
    rw [realTarget_coeff]
    simp only [computedCosCoefficients, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    by_cases hj : j < n
    · simp only [dif_pos hj, Option.getD_some]
      simp only [apply_ite, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg, Rat.cast_one,
          Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_zero]
      have hc := (computed_signal_trig_scalar_coefficients t j).1
      simp only [Rat.cast_neg, Rat.cast_one, Rat.cast_natCast] at hc
      rw [hc]
      simp [hamiltonianCosine, cosineTaylorPolynomial, Polynomial.coeff_C_mul,
        Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, hj]
    · simp [hj, hamiltonianCosine, cosineTaylorPolynomial, Polynomial.coeff_C_mul,
        Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  · ext j
    rw [realTarget_coeff]
    simp only [computedSinCoefficients, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    by_cases hj : j < n
    · simp only [dif_pos hj, Option.getD_some]
      simp only [apply_ite, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg, Rat.cast_one,
          Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_zero]
      have hc := (computed_signal_trig_scalar_coefficients t j).2
      simp only [Rat.cast_neg, Rat.cast_one, Rat.cast_natCast] at hc
      rw [hc]
      simp [hamiltonianSine, sineTaylorPolynomial, Polynomial.coeff_C_mul,
        Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, hj]
    · simp [hj, hamiltonianSine, sineTaylorPolynomial, Polynomial.coeff_C_mul,
        Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]

/-- The computed segment count is positive and the absolute value of the time per segment is at
most 1/2. -/
theorem computed_signal_segment_size (t : ℚ) :
    0 < computedSignalSegments t ∧ |(t:ℝ)/(computedSignalSegments t:ℝ)| ≤ 1/2 := by
  have hr : 0 < computedSignalSegments t := by
    unfold computedSignalSegments
    exact lt_of_lt_of_le (by omega : 0 < 1) (le_max_left _ _)
  have ht : 2*|t| ≤ (computedSignalSegments t:ℚ) :=
    (Nat.le_ceil (2*|t|)).trans (by exact_mod_cast le_max_right 1 ⌈2*|t|⌉₊)
  have ht' : 2*|(t:ℝ)| ≤ (computedSignalSegments t:ℝ) := by exact_mod_cast ht
  refine ⟨hr,?_⟩
  rw [abs_div, abs_of_pos (show (0:ℝ) < (computedSignalSegments t:ℝ) by exact_mod_cast hr)]
  apply (div_le_iff₀ (by exact_mod_cast hr)).mpr
  linarith

/-- The total budget r√(6750 · 16 · 2^(−32(k + ⌈log₂ r⌉ + 16))) is at most 2^(−k) for natural r
and k, using `Nat.clog` for the logarithm. -/
theorem computed_signal_geometric_budget (r k : ℕ) :
    (r:ℝ) * Real.sqrt (6750*(16*(1/2:ℝ)^(32*(k+Nat.clog 2 r+16)))) ≤ (1/2:ℝ)^k := by
  let l := Nat.clog 2 r
  let a : ℝ := (1/2:ℝ)^(16*(k+l+16))
  have ha : 0 ≤ a := by positivity
  have he : (1/2:ℝ)^(32*(k+l+16)) = a^2 := by
    dsimp [a]
    rw [show 32*(k+l+16) = (16*(k+l+16))*2 by omega, pow_mul]
  have hroot : Real.sqrt (6750*(16*(1/2:ℝ)^(32*(k+l+16)))) ≤ 512*a := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [he]
    nlinarith [sq_nonneg a]
  have hsmall : a ≤ (1/2:ℝ)^(k+l+9) := by
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    omega
  have hr : (r:ℝ) ≤ (2:ℝ)^l := by exact_mod_cast Nat.le_pow_clog (by norm_num) r
  have hrl : (r:ℝ)*(1/2:ℝ)^l ≤ 1 := by
    have hid : (2:ℝ)^l*(1/2:ℝ)^l = 1 := by rw [← mul_pow]; norm_num
    exact (mul_le_mul_of_nonneg_right hr (by positivity)).trans hid.le
  calc
    _ ≤ (r:ℝ)*(512*a) := mul_le_mul_of_nonneg_left hroot (Nat.cast_nonneg r)
    _ ≤ (r:ℝ)*(512*(1/2:ℝ)^(k+l+9)) := by gcongr
    _ = (1/2:ℝ)^k*((r:ℝ)*(1/2:ℝ)^l) := by
      simp only [pow_add]
      norm_num
      ring
    _ ≤ (1/2:ℝ)^k := by nlinarith [mul_le_mul_of_nonneg_left hrl (by positivity : 0 ≤ (1/2:ℝ)^k)]

/-- The computed segment count, cutoff, and tolerance are positive, the time per segment has
absolute value at most 1/2, and its Taylor error is at most 2 · 2^(−n). The accumulated
square-root error budget is at most 2^(−k). -/
theorem computed_signal_explicit_segment_precision : ∀ (t : ℚ) (k : ℕ),
    let r := computedSignalSegments t
    let n := computedSignalCutoff t k
    0 < r ∧ 0 < n ∧ |(t:ℝ)/(r:ℝ)| ≤ 1/2 ∧ 0 < computedSignalTolerance t k ∧
    exponentialTaylorError ((t:ℝ)/(r:ℝ)) n ≤ 2*(1/2:ℝ)^n ∧
    (r:ℝ)*Real.sqrt (6750*(16*(1/2:ℝ)^n)) ≤ (1/2:ℝ)^k := by
  intro t k
  (try dsimp only)
  obtain ⟨hr,ht⟩ := computed_signal_segment_size t
  refine ⟨hr,by unfold computedSignalCutoff; omega,ht,?_,?_,?_⟩
  · unfold computedSignalTolerance
    positivity
  · unfold exponentialTaylorError
    have hn : (1:ℝ) ≤ ((computedSignalCutoff t k).factorial:ℝ) := by
      exact_mod_cast Nat.factorial_pos (computedSignalCutoff t k)
    calc
      _ ≤ |(t:ℝ)/(computedSignalSegments t:ℝ)|^(computedSignalCutoff t k)*2 := by
        gcongr
        exact div_le_self (by positivity) hn
      _ ≤ (1/2:ℝ)^(computedSignalCutoff t k)*2 := by gcongr
      _ = _ := by ring
  · exact computed_signal_geometric_budget (computedSignalSegments t) k

/-- The complex algebra homomorphism sending a function of spectral values to its diagonal
operator in the orthonormal basis b. -/
noncomputable def computedSignalSpectralHom {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I)) :
    (J → ℂ) →ₐ[ℂ] Matrix I I ℂ where
  toFun := spectralDiagonal b
  map_zero' := by simp [spectralDiagonal]
  map_one' := by simpa using! spectralDiagonal_const b 1
  map_add' f g := by
    have hd : Matrix.diagonal (f+g) = Matrix.diagonal f + Matrix.diagonal g := by
      ext i j
      by_cases hij : i=j <;> simp [Matrix.diagonal, Matrix.of_apply, hij]
    simp only [spectralDiagonal, hd, Matrix.mul_add, Matrix.add_mul]
  map_mul' f g := by
    have hd : Matrix.diagonal (f*g) = Matrix.diagonal f * Matrix.diagonal g := by
      rw [Matrix.diagonal_mul_diagonal]
      rfl
    simp only [spectralDiagonal, hd, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (basisColumns b)ᴴ (basisColumns b), basisColumns_adjoint_mul,
      Matrix.one_mul]
  commutes' c := by
    have hsrc : algebraMap ℂ (J → ℂ) c = fun _ => c := by
      ext j
      simp
    rw [hsrc, Algebra.algebraMap_eq_smul_one]
    exact spectralDiagonal_const b c

/-- Exponentiating a matrix diagonal in an orthonormal basis exponentiates each of its spectral
values. -/
theorem computed_signal_spectral_exp {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I))
    (f : J → ℂ) :
    NormedSpace.exp (spectralDiagonal b f) =
      spectralDiagonal b (fun j => NormedSpace.exp (f j)) := by
  have h := NormedSpace.map_exp (computedSignalSpectralHom b)
    (computedSignalSpectralHom b).toLinearMap.continuous_of_finiteDimensional f
  simpa only [computedSignalSpectralHom, Pi.exp_def] using! h.symm

/-- A uniform scalar error bound ε ≥ 0 for approximating exp(−itx) on [−1, 1] gives the same
operator norm bound for polynomial evaluation at a Hermitian contraction A. -/
theorem computed_signal_hermitian_polynomial_error {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (hNorm : ‖A‖ ≤ 1)
    (p : Polynomial ℂ) (t ε : ℝ) (hε : 0 ≤ ε)
    (hscalar : ∀ x ∈ Set.Icc (-1:ℝ) 1,
      ‖p.eval (x:ℂ) - Complex.exp (-Complex.I*(t:ℂ)*(x:ℂ))‖ ≤ ε) :
    ‖Polynomial.aeval A p - hamiltonianEvolution A t‖ ≤ ε := by
  let b := hA.eigenvectorBasis
  let f : I → ℂ := fun i => (hA.eigenvalues i:ℂ)
  have hf (i : I) : A.toEuclideanLin (b i) = f i • b i := by
    ext j
    simpa [b,f,Pi.smul_apply,smul_eq_mul] using! congrFun (hA.mulVec_eigenvectorBasis i) j
  have hdiag : A = spectralDiagonal b f := eq_spectralDiagonal_of_action b A f hf
  have hexp : hamiltonianEvolution A t =
      spectralDiagonal b (fun i => Complex.exp (-Complex.I*(t:ℂ)*f i)) := by
    rw [hamiltonianEvolution,hdiag]
    have hscale := (computedSignalSpectralHom b).toLinearMap.map_smul (-Complex.I*(t:ℂ)) f
    change spectralDiagonal b ((-Complex.I*(t:ℂ)) • f) =
      (-Complex.I*(t:ℂ)) • spectralDiagonal b f at hscale
    rw [← hscale, computed_signal_spectral_exp]
    simp only [Pi.smul_apply, smul_eq_mul, ← Complex.exp_eq_exp_ℂ]
  rw [aeval_eq_spectralDiagonal_of_action b A f hf p,hexp]
  apply spectralDiagonal_error_le b _ _ hε
  intro i
  have hi : |hA.eigenvalues i| ≤ 1 := by
    letI : Nonempty I := ⟨i⟩
    have he := spectrum.norm_le_norm_of_mem (hA.eigenvalues_mem_spectrum_real i)
    have he' : |hA.eigenvalues i| ≤ ‖A‖ := by simpa only [Real.norm_eq_abs] using! he
    exact he'.trans hNorm
  exact hscalar (hA.eigenvalues i) (abs_le.mp hi)

/-- Both finite synthesis runs return phase packets of lengths 2n and 2n + 1 with unit-modulus
phase data. Their real response polynomials approximate the segment cosine and sine targets
uniformly on [−1, 1] within 2^(−n). -/
theorem computed_signal_synthesized_packets (t : ℚ) (k : ℕ) :
    let n := computedSignalCutoff t k
    let u := t/(computedSignalSegments t:ℚ)
    ∃ c s : PhaseData,
      (finitePhaseSynthesis (computedCosCoefficients u n) (2*n) (computedSignalTolerance t k)).value = some c ∧
      (finitePhaseSynthesis (computedSinCoefficients u n) (2*n+1) (computedSignalTolerance t k)).value = some s ∧
      c.phases.length = 2*n ∧ s.phases.length = 2*n+1 ∧
      (IsPhase (gaussianRatComplex c.base) ∧ ∀ z ∈ c.phases.map gaussianRatComplex, IsPhase z) ∧
      (IsPhase (gaussianRatComplex s.base) ∧ ∀ z ∈ s.phases.map gaussianRatComplex, IsPhase z) ∧
      (∀ x ∈ Set.Icc (-1:ℝ) 1,
        |((responseP (gaussianRatComplex c.base) (c.phases.map gaussianRatComplex)).eval (x:ℂ)).re -
          (hamiltonianCosine (u:ℝ) n).eval x| ≤ (1/2:ℝ)^n) ∧
      (∀ x ∈ Set.Icc (-1:ℝ) 1,
        |((responseP (gaussianRatComplex s.base) (s.phases.map gaussianRatComplex)).eval (x:ℂ)).re -
          (hamiltonianSine (u:ℝ) n).eval x| ≤ (1/2:ℝ)^n) := by
  let n := computedSignalCutoff t k
  let u := t/(computedSignalSegments t:ℚ)
  have hu : (u:ℝ) = (t:ℝ)/(computedSignalSegments t:ℝ) := by simp [u]
  have hc := computed_signal_native_trig_coefficients u n
  obtain ⟨_,hn,ht,hε,hrem,_⟩ := computed_signal_explicit_segment_precision t k
  have hn2 : 2 ≤ n := by dsimp [n,computedSignalCutoff]; omega
  have hrem1 : exponentialTaylorError (u:ℝ) n < 1 := by
    have hp : (1/2:ℝ)^n ≤ (1/2:ℝ)^2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn2
    rw [← hu] at hrem
    dsimp only [n] at hp
    norm_num at hp
    linarith
  have htime : 2*|(u:ℝ)| ≤ (n:ℝ)+1 := by
    rw [← hu] at ht
    have hn' : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hcd : (realTarget (computedCosCoefficients u n)).degree ≤ ((2*n:ℕ):WithBot ℕ) := by
    rw [hc.1]
    apply Polynomial.degree_le_of_natDegree_le
    exact (Polynomial.natDegree_C_mul_le (1/4:ℝ) (cosineTaylorPolynomial (u:ℝ) n)).trans
      ((cosineTaylorPolynomial_natDegree_le (u:ℝ) n).trans (by omega))
  have hsd : (realTarget (computedSinCoefficients u n)).degree ≤ ((2*n+1:ℕ):WithBot ℕ) := by
    rw [hc.2.1]
    apply Polynomial.degree_le_of_natDegree_le
    exact (Polynomial.natDegree_C_mul_le (1/4:ℝ) (sineTaylorPolynomial (u:ℝ) n)).trans
      ((sineTaylorPolynomial_natDegree_le (u:ℝ) n).trans (by omega))
  have hcp : Qatlib.Concepts.QspSimulation.Achievability.HasRealParity (2*n) (realTarget (computedCosCoefficients u n)) := by
    rw [hc.1]
    simp [Qatlib.Concepts.QspSimulation.Achievability.HasRealParity, hamiltonianCosine,
        cosineTaylorPolynomial_comp_neg_X, pow_mul]
  have hsp : Qatlib.Concepts.QspSimulation.Achievability.HasRealParity (2*n+1) (realTarget (computedSinCoefficients u n)) := by
    rw [hc.2.1]
    simp [Qatlib.Concepts.QspSimulation.Achievability.HasRealParity, hamiltonianSine,
        sineTaylorPolynomial_comp_neg_X, pow_add,pow_mul]
  obtain ⟨c,hcOut,hcLen,hcBase,hcPhase,_,hcApprox,_⟩ :=
    finite_rational_phase_synthesis_terminates (computedCosCoefficients u n) (2*n)
      (computedSignalTolerance t k) hε hcd hcp (by
        rw [hc.1]
        intro x hx
        exact (scaledCosineTaylorPolynomial_abs_lt_half (u:ℝ) n htime hrem1 hx).le.trans
            (by norm_num))
  obtain ⟨s,hsOut,hsLen,hsBase,hsPhase,_,hsApprox,_⟩ :=
    finite_rational_phase_synthesis_terminates (computedSinCoefficients u n) (2*n+1)
      (computedSignalTolerance t k) hε hsd hsp (by
        rw [hc.2.1]
        intro x hx
        exact (scaledSineTaylorPolynomial_abs_lt_half (u:ℝ) n htime hrem1 hx).le.trans
            (by norm_num))
  refine ⟨c,s,hcOut,hsOut,hcLen,hsLen,data_phase_valid c hcBase hcPhase,
    data_phase_valid s hsBase hsPhase,?_,?_⟩
  · simpa only [hc.1, computedSignalTolerance, Rat.cast_pow, Rat.cast_div, Rat.cast_one,
      Rat.cast_ofNat, Rat.cast_natCast, n, u] using! hcApprox
  · simpa only [hc.2.1, computedSignalTolerance, Rat.cast_pow, Rat.cast_div, Rat.cast_one,
      Rat.cast_ofNat, Rat.cast_natCast, n, u] using! hsApprox

/-- Four times the difference between the real-part cosine response polynomial and i times the
real-part sine response polynomial from packets c and s. -/
noncomputable def computedSignalResponsePolynomial (c s : PhaseData) : Polynomial ℂ :=
  Polynomial.C 4 * (realPartPolynomial (responseP (gaussianRatComplex c.base) (c.phases.map gaussianRatComplex)) -
    Polynomial.C Complex.I * realPartPolynomial (responseP (gaussianRatComplex s.base) (s.phases.map gaussianRatComplex)))

/-- If both real response polynomials approximate their Hamiltonian trigonometric targets within
ε on [−1, 1] and 2|t| ≤ n + 1, their combined response approximates exp(−itx) within 8ε plus
`exponentialTaylorError t n`. -/
theorem computed_signal_response_pair_scalar_bound (t ε : ℝ) (n : ℕ) (c s : PhaseData)
    (_hε : 0 ≤ ε) (ht : 2*|t| ≤ (n:ℝ)+1)
    (hc : ∀ x ∈ Set.Icc (-1:ℝ) 1,
      |((responseP (gaussianRatComplex c.base) (c.phases.map gaussianRatComplex)).eval (x:ℂ)).re -
        (hamiltonianCosine t n).eval x| ≤ ε)
    (hs : ∀ x ∈ Set.Icc (-1:ℝ) 1,
      |((responseP (gaussianRatComplex s.base) (s.phases.map gaussianRatComplex)).eval (x:ℂ)).re -
        (hamiltonianSine t n).eval x| ≤ ε) :
    ∀ x ∈ Set.Icc (-1:ℝ) 1,
      ‖(computedSignalResponsePolynomial c s).eval (x:ℂ) - Complex.exp (-Complex.I*(t:ℂ)*(x:ℂ))‖ ≤
        8*ε + exponentialTaylorError t n := by
  intro x hx
  let a : ℝ :=
      ((responseP (gaussianRatComplex c.base) (c.phases.map gaussianRatComplex)).eval (x:ℂ)).re
  let b : ℝ :=
      ((responseP (gaussianRatComplex s.base) (s.phases.map gaussianRatComplex)).eval (x:ℂ)).re
  let ac : ℝ := (hamiltonianCosine t n).eval x
  let bs : ℝ := (hamiltonianSine t n).eval x
  have ha : ‖(a:ℂ)-(ac:ℂ)‖ ≤ ε := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    exact hc x hx
  have hb : ‖(b:ℂ)-(bs:ℂ)‖ ≤ ε := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    exact hs x hx
  have he : (exponentialTaylorPolynomial t n).eval (x:ℂ) = 4*((ac:ℂ)-Complex.I*(bs:ℂ)) := by
    rw [exponentialTaylorPolynomial_eval_eq_trig]
    dsimp [ac,bs,hamiltonianCosine,hamiltonianSine]
    simp only [Polynomial.eval_mul,Polynomial.eval_C]
    push_cast
    ring
  have hp : (computedSignalResponsePolynomial c s).eval (x:ℂ) = 4*((a:ℂ)-Complex.I*(b:ℂ)) := by
    simp only [computedSignalResponsePolynomial, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_sub, realPartPolynomial_eval]
    rfl
  have hdiff : ‖(computedSignalResponsePolynomial c s).eval (x:ℂ) -
      (exponentialTaylorPolynomial t n).eval (x:ℂ)‖ ≤ 8*ε := by
    rw [hp,he,show (4:ℂ)*((a:ℂ)-Complex.I*(b:ℂ)) - 4*((ac:ℂ)-Complex.I*(bs:ℂ)) =
      4*(((a-ac:ℝ):ℂ)-Complex.I*((b-bs:ℝ):ℂ)) by push_cast; ring]
    rw [norm_mul]
    norm_num
    have htri := norm_sub_le ((a:ℂ)-(ac:ℂ)) (Complex.I*((b:ℂ)-(bs:ℂ)))
    rw [norm_mul,Complex.norm_I,one_mul] at htri
    nlinarith
  exact (norm_sub_le_norm_sub_add_norm_sub _ ((exponentialTaylorPolynomial t n).eval (x:ℂ)) _).trans
    (add_le_add hdiff (exponentialTaylorPolynomial_error_le t n ht hx))

/-- For a Hermitian projected unitary encoding, both segment phase searches succeed and the
computed body is well formed. It block encodes the segment evolution with scale 8 and error
16 · 2^(−n), using exactly 4n + 1 oracle queries and 4n + 6 gates. -/
theorem computed_signal_phase_packets_and_body : ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
  (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ) (t : ℚ) (k : ℕ),
  A.IsHermitian → ProjectedUnitaryEncoding A U F F →
  let n := computedSignalCutoff t k
  let u := t/(computedSignalSegments t:ℚ)
  (∃ c s : PhaseData,
    (finitePhaseSynthesis (computedCosCoefficients u n) (2*n) (computedSignalTolerance t k)).value=some c ∧
    (finitePhaseSynthesis (computedSinCoefficients u n) (2*n+1) (computedSignalTolerance t k)).value=some s) ∧
  WellFormedAdjointCircuit (computedSignalBody F t k) ∧
  BlockEncoding (hamiltonianEvolution A (u:ℝ))
    (evaluate (controlOracle (parallelOracle (J:=Bool) U)) (computedSignalBody F t k))
    (hamiltonianFrame F) (hamiltonianFrame F) 8 (16*(1/2:ℝ)^n) ∧
  adjointQueryCount (computedSignalBody F t k)=4*n+1 ∧ adjointGateCount (computedSignalBody F t k)=4*n+6 := by
  intro H I _ _ _ _ A U F t k hA h
  (try dsimp only)
  let n := computedSignalCutoff t k
  let u := t/(computedSignalSegments t:ℚ)
  obtain ⟨c,s,hcOut,hsOut,hcLen,hsLen,hcPh,hsPh,hcApprox,hsApprox⟩ :=
    computed_signal_synthesized_packets t k
  have hu : (u:ℝ) = (t:ℝ)/(computedSignalSegments t:ℝ) := by simp [u]
  obtain ⟨_,_,ht,_,hrem,_⟩ := computed_signal_explicit_segment_precision t k
  rw [← hu] at ht hrem
  have htime : 2*|(u:ℝ)| ≤ (n:ℝ)+1 := by
    have hn' : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hnorm : ‖A‖ ≤ 1 := by
    rw [← h.encoded]
    exact l2_norm_compress_le_one h.left_isometry h.unitary h.right_isometry
  have herr : ‖Polynomial.aeval A (computedSignalResponsePolynomial c s) - hamiltonianEvolution A (u:ℝ)‖ ≤
      16*(1/2:ℝ)^n := by
    apply computed_signal_hermitian_polynomial_error A hA hnorm _ _ _ (by positivity)
    intro x hx
    have he := computed_signal_response_pair_scalar_bound (u:ℝ) ((1/2:ℝ)^n) n c s
      (by positivity) htime hcApprox hsApprox x hx
    exact he.trans (by nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) n])
  have hcos := hermitian_realPart_projectedEncoding hA h hcPh.1
    (c.phases.map gaussianRatComplex) hcPh.2
  have hsin := hermitian_realPart_projectedEncoding hA h hsPh.1
    (s.phases.map gaussianRatComplex) hsPh.2
  have hactual := average_projectedEncoding hcos
    (hamiltonian_phase_projectedEncoding hsin (z := -Complex.I) (by simp [IsPhase]))
  have hcombine : (8:ℝ) • ((2:ℂ)⁻¹ •
      (Polynomial.aeval A (realPartPolynomial (responseP (gaussianRatComplex c.base) (c.phases.map gaussianRatComplex))) +
        (-Complex.I) • Polynomial.aeval A
          (realPartPolynomial (responseP (gaussianRatComplex s.base) (s.phases.map gaussianRatComplex))))) =
      Polynomial.aeval A (computedSignalResponsePolynomial c s) := by
    simp only [computedSignalResponsePolynomial, map_mul, map_sub, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]
    ext i j
    norm_num [Matrix.smul_apply, Complex.real_smul]
    ring
  have hbody : computedSignalBody F t k = compileHamiltonian F
      (gaussianRatComplex c.base) (c.phases.map gaussianRatComplex)
      (gaussianRatComplex s.base) (s.phases.map gaussianRatComplex) := by
    dsimp only [computedSignalBody]
    rw [hcOut,hsOut]
  have hWF : WellFormedAdjointCircuit (computedSignalBody F t k) := by
    rw [hbody]
    exact compileHamiltonian_wellFormed h.left_isometry hcPh.1 _ hcPh.2 hsPh.1 _ hsPh.2
  have hBE : BlockEncoding (hamiltonianEvolution A (u:ℝ))
      (evaluate (controlOracle (parallelOracle (J:=Bool) U)) (computedSignalBody F t k))
      (hamiltonianFrame F) (hamiltonianFrame F) 8 (16*(1/2:ℝ)^n) := by
    rw [hbody,evaluate_compileHamiltonian]
    refine ⟨hactual.unitary,hactual.left_isometry,hactual.right_isometry,by norm_num,by positivity,?_⟩
    dsimp only [hamiltonianCircuit,hamiltonianFrame]
    rw [hactual.encoded,hcombine,norm_sub_rev]
    exact herr
  refine ⟨⟨c,s,hcOut,hsOut⟩,hWF,hBE,?_,?_⟩
  · rw [hbody,(counts_compileHamiltonian F _ _ _ _).1,List.length_map,List.length_map,hcLen,hsLen]
    omega
  · rw [hbody,(counts_compileHamiltonian F _ _ _ _).2,List.length_map,List.length_map,hcLen,hsLen]
    omega

/-- For a Hermitian projected unitary encoding and any input state, the amplified computed
segment approximates the encoded segment evolution with vector norm error at most √(6750 ·
16 · 2^(−n)) times the input norm, where n is the computed cutoff. -/
theorem computed_signal_same_clean_segment : ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
  (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ) (t : ℚ) (k : ℕ),
  A.IsHermitian → ProjectedUnitaryEncoding A U F F →
  ∀ ψ : QState I,
  ‖toEuclidean_fromVec (evaluate (TensorGate (1 : Matrix Bool Bool ℂ)
      (controlOracle (parallelOracle (J:=Bool) U)))
    (scaleEightAmplifyWord (hamiltonianFrame F) (computedSignalBody F t k))*ᵥ
      (scaleEightFrame (hamiltonianFrame F)*ᵥψ) -
    scaleEightFrame (hamiltonianFrame F)*ᵥ
      (hamiltonianEvolution A ((t:ℝ)/(computedSignalSegments t:ℝ))*ᵥψ))‖ ≤
    Real.sqrt (6750*(16*(1/2:ℝ)^computedSignalCutoff t k))*‖toEuclidean_fromVec ψ‖ := by
  intro H I _ _ _ _ A U F t k hA h ψ
  have hb := computed_signal_phase_packets_and_body H I A U F t k hA h
  let u : ℚ := t/(computedSignalSegments t:ℚ)
  have he := scale_eight_noisy_clean_workspace_bound (Bool×(Bool×H)) I
    (controlOracle (parallelOracle (J:=Bool) U)) (hamiltonianFrame F)
    (computedSignalBody F t k)
    (hamiltonianEvolution A (u:ℝ))
    (16*(1/2:ℝ)^computedSignalCutoff t k)
    (controlOracle_unitary (parallelOracle_unitary h.unitary)) hb.2.1
    (hamiltonianEvolution_unitary hA _) hb.2.2.1 ψ
  simpa only [u, Rat.cast_div, Rat.cast_natCast] using! he

end Qatlib.Concepts.QspSimulation.JacobiAnger
