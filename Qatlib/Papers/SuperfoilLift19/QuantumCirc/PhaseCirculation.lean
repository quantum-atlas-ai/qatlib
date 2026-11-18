/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum.Basic

@[expose] public section

/-!
# Phase lifts and quantized circulation

[Musser2019Superfoil], p. 154502-2, uses the Madelung velocity
`u = (hbar / mass) grad phase` and the circulation quantum `2 pi hbar / mass`.
See [the published article](https://doi.org/10.1103/PhysRevLett.123.154502).

Here a phase lift is a real differentiable function along a parametrized loop.
The endpoint phase increment is an integer multiple of `2 pi`. The fundamental
theorem of calculus then proves circulation quantization; the integer increment
is an explicit hypothesis, rather than an unproved assertion about arbitrary
loops. The complex polar factor is single valued after an integer turn and
multiplies according to addition of phase. No existence theorem for a phase lift
through a density zero, vortex nucleation, or Gross--Pitaevskii evolution is
asserted.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.SuperfoilLift19.QuantumCirc

/-- A unit complex polar factor with a real phase. -/
def phaseFactor (phase : ℝ) : ℂ := Complex.exp ((phase : ℂ) * Complex.I)

/-- A polar phase factor has unit norm. -/
theorem phase_factor_norm (phase : ℝ) : ‖phaseFactor phase‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I phase

/-- The wave amplitude and phase in a complex polar representation. -/
def polarWave (amplitude phase : ℝ) : ℂ := (amplitude : ℂ) * phaseFactor phase

/-- The squared norm of a polar wave is the squared real amplitude,
independently of its phase. -/
theorem polar_wave_density (amplitude phase : ℝ) :
    ‖polarWave amplitude phase‖ ^ 2 = amplitude ^ 2 := by
  simp [polarWave, phase_factor_norm, sq_abs]

/-- Multiplication of polar factors adds their real phases. -/
theorem phase_factor_add (a b : ℝ) :
    phaseFactor (a + b) = phaseFactor a * phaseFactor b := by
  simp only [phaseFactor, Complex.ofReal_add, add_mul, Complex.exp_add]

/-- A complete integer turn leaves the polar factor unchanged. -/
theorem phase_factor_integer_turn (phase : ℝ) (n : ℤ) :
    phaseFactor (phase + 2 * Real.pi * (n : ℝ)) = phaseFactor phase := by
  rw [phase_factor_add]
  have h : phaseFactor (2 * Real.pi * (n : ℝ)) = 1 := by
    unfold phaseFactor
    have hexponent : ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I =
        (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [hexponent, Complex.exp_int_mul_two_pi_mul_I]
  rw [h, mul_one]

/-- Equality of complex endpoint phases is equivalent to an integer real phase
increment. This derives the winding condition from single-valued polar data. -/
theorem phase_factor_closure_iff_winding (a b : ℝ) :
    phaseFactor b = phaseFactor a ↔ ∃ n : ℤ, b - a = 2 * Real.pi * (n : ℝ) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
    have him := congrArg Complex.im hn
    simp at him
    exact ⟨n, by linarith⟩
  · rintro ⟨n, hn⟩
    have hb : b = a + 2 * Real.pi * (n : ℝ) := by linarith
    rw [hb]
    exact phase_factor_integer_turn a n

/-- Away from zero amplitude, a single-valued complex polar wave has exactly
an integer endpoint phase increment. The nonzero-amplitude condition is
essential because zero waves carry no phase information. -/
theorem polar_wave_closure_iff_winding {amplitude : ℝ} (hamplitude : amplitude ≠ 0)
    (a b : ℝ) : polarWave amplitude b = polarWave amplitude a ↔
      ∃ n : ℤ, b - a = 2 * Real.pi * (n : ℝ) := by
  have hcomplex : (amplitude : ℂ) ≠ 0 := by exact_mod_cast hamplitude
  constructor
  · intro h
    apply (phase_factor_closure_iff_winding a b).1
    exact mul_left_cancel₀ hcomplex h
  · intro h
    exact congrArg (fun z : ℂ => (amplitude : ℂ) * z)
      ((phase_factor_closure_iff_winding a b).2 h)

/-- The positive-orientation circulation quantum; the mass is assumed positive
only in results that need a nonzero or positive quantum. -/
def circulationQuantum (hbar mass : ℝ) : ℝ := 2 * Real.pi * hbar / mass

/-- Circulation of an integer winding in the Madelung normalization. -/
def quantizedCirculation (hbar mass : ℝ) (winding : ℤ) : ℝ :=
  circulationQuantum hbar mass * (winding : ℝ)

/-- The circulation quantum is positive for positive Planck scale and mass. -/
theorem circulation_quantum_pos {hbar mass : ℝ} (hhbar : 0 < hbar)
    (hmass : 0 < mass) : 0 < circulationQuantum hbar mass := by
  exact div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hhbar) hmass

/-- Integer windings compose additively at the circulation level. -/
theorem quantized_circulation_add (hbar mass : ℝ) (m n : ℤ) :
    quantizedCirculation hbar mass (m + n) =
      quantizedCirculation hbar mass m + quantizedCirculation hbar mass n := by
  simp only [quantizedCirculation, Int.cast_add, mul_add]

/-- Reversing the winding reverses the circulation. -/
theorem quantized_circulation_neg (hbar mass : ℝ) (n : ℤ) :
    quantizedCirculation hbar mass (-n) = -quantizedCirculation hbar mass n := by
  simp [quantizedCirculation]

/-- The total circulation of finitely many vortices is the circulation of their
total integer winding. -/
theorem quantized_circulation_sum {ι : Type*} (s : Finset ι)
    (hbar mass : ℝ) (winding : ι → ℤ) :
    quantizedCirculation hbar mass (∑ i ∈ s, winding i) =
      ∑ i ∈ s, quantizedCirculation hbar mass (winding i) := by
  simp [quantizedCirculation, Finset.mul_sum]

/-- For a nonzero circulation quantum, the observed circulation determines the
integer winding uniquely. -/
theorem quantized_circulation_injective {hbar mass : ℝ}
    (hquantum : circulationQuantum hbar mass ≠ 0) :
    Function.Injective (quantizedCirculation hbar mass) := by
  intro m n h
  have hcast : (m : ℝ) = (n : ℝ) := mul_left_cancel₀ hquantum h
  exact_mod_cast hcast

/-- Integrating the tangential Madelung velocity along a differentiable real
phase lift gives an integer circulation quantum when its endpoint increment is
an integer turn. Integrability and the phase derivative are explicit analytic
hypotheses. -/
theorem phase_integral_quantized (hbar mass a b : ℝ) (phase velocity : ℝ → ℝ)
    (n : ℤ)
    (hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt phase (velocity t) t)
    (hint : IntervalIntegrable velocity MeasureTheory.volume a b)
    (hwinding : phase b - phase a = 2 * Real.pi * (n : ℝ)) :
    (∫ t in a..b, (hbar / mass) * velocity t) =
      quantizedCirculation hbar mass n := by
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, hwinding]
  unfold quantizedCirculation circulationQuantum
  ring

/-- A differentiable phase lift with equal complex endpoints necessarily has
quantized circulation; the integer is obtained from complex exponential
periodicity, not supplied as a quantization hypothesis. -/
theorem closed_phase_integral_quantized (hbar mass a b : ℝ) (phase velocity : ℝ → ℝ)
    (hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt phase (velocity t) t)
    (hint : IntervalIntegrable velocity MeasureTheory.volume a b)
    (hclosed : phaseFactor (phase b) = phaseFactor (phase a)) :
    ∃ n : ℤ, (∫ t in a..b, (hbar / mass) * velocity t) =
      quantizedCirculation hbar mass n := by
  obtain ⟨n, hn⟩ := (phase_factor_closure_iff_winding (phase a) (phase b)).1 hclosed
  exact ⟨n, phase_integral_quantized hbar mass a b phase velocity n hderiv hint hn⟩

/-- An oppositely wound starting vortex cancels the bound circulation exactly;
this is a kinematic pair law and asserts no vortex-shedding dynamics. -/
theorem starting_vortex_cancellation (hbar mass : ℝ) (n : ℤ) :
    quantizedCirculation hbar mass n + quantizedCirculation hbar mass (-n) = 0 := by
  rw [quantized_circulation_neg, add_neg_cancel]

/-- Emitting a vortex of winding `k` and changing the bound winding by `-k`
preserves the sum of bound and wake circulation. -/
theorem shedding_preserves_total_circulation (hbar mass : ℝ) (bound wake k : ℤ) :
    quantizedCirculation hbar mass (bound - k) +
        quantizedCirculation hbar mass (wake + k) =
      quantizedCirculation hbar mass bound + quantizedCirculation hbar mass wake := by
  simp only [quantizedCirculation, Int.cast_sub, Int.cast_add]
  ring

end Qatlib.Papers.SuperfoilLift19.QuantumCirc
