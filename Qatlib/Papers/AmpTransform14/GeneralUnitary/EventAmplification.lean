/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.OperatorErrors.OperatorError
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Tactic

@[expose] public section

/-!
# Amplification with a general flat unitary

Section 2.13 of [Cornwell2014], printed pp. 53-55, allows any unitary in place of the Fourier
transform. Here the main interface uses the flat specialization from Section 2.14. For a
label `y` at which the row of `U` sums to zero and whose marked row sum is nonzero, the two
algorithm executions (one with the oracle state and one after the Grover rounds) have the exact
amplitude ratio `-sqrt N * (a_k - b_k) / 2`, and hence the probability ratio
`N ^ 2 / (4 M ^ 2) * tan ^ 2 θ * sin ^ 2 (2 k θ)`.  These are the same formulas the source
obtains when `U` is the Fourier matrix.

The marked and amplified coefficient vectors are genuine elements of
`EuclideanSpace ℂ (Fin N)`.  The pointwise row-sum hypotheses are the source's
`∑ z, α(y,z) = 0` and `∑ z ∈ A, α(y,z) ≠ 0`; the uniform constant `1/4` is outside the
universal quantifiers.  The theorem does not claim the source's separate general amplification
procedure of Section 2.14, nor any gate, query or ancilla cost.

## Main statements

* `sum_markedWeight`, `sum_amplifiedWeight`: the two finite coefficient sums reduce to the
  marked row sum when the row sums to zero.
* `general_unitary_amplitude_ratio`: the exact amplitude ratio from the row-sum hypotheses.
* `general_unitary_event_amplification`: the uniform-constant probability-ratio statement at
  the source's floor round count.

## References

* [Cornwell, 2014][Cornwell2014], Section 2.13, printed pp. 53-55,
  [arXiv:1406.0190](https://arxiv.org/abs/1406.0190)
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.AmpTransform14.GeneralUnitary

/-- The Grover angle `arcsin (sqrt (M / N))` of the amplified transform. -/
noncomputable def generalUnitaryAngle (N M : ℕ) : ℝ :=
  Real.arcsin (Real.sqrt ((M : ℝ) / (N : ℝ)))

/-- The source's floor round count `⌊π / (4 θ)⌋` at the Grover angle. -/
noncomputable def generalUnitaryRounds (N M : ℕ) : ℕ :=
  Nat.floor (Real.pi / (4 * generalUnitaryAngle N M))

/-- The marked coefficient vector of the oracle state: `-1` on the marked set and `1` elsewhere.
Adding the all-ones vector gives the source's `(-2) ∑_{z ∈ A} |z> + ∑_{z} |z>`. -/
noncomputable def markedWeight {N : ℕ} (A : Finset (Fin N)) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 fun z => if z ∈ A then (-1 : ℂ) else 1

/-- The coefficient vector after the Grover rounds: `a` on the marked set and `b` elsewhere. -/
noncomputable def amplifiedWeight {N : ℕ} (A : Finset (Fin N)) (a b : ℝ) :
    EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 fun z => if z ∈ A then (a : ℂ) else (b : ℂ)

/-- The unamplified output amplitude after the oracle state and the flat unitary, including the
source's `1 / sqrt N` normalization of the oracle state. -/
noncomputable def markedAmplitude {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (A : Finset (Fin N)) (y : Fin N) : ℂ :=
  ((Real.sqrt (N : ℝ) : ℂ))⁻¹ * ∑ z, U y z * (if z ∈ A then (-1 : ℂ) else 1)

/-- The amplified output amplitude after the Grover state and the flat unitary.  The factor
`1 / sqrt N` already sits in the entries of `U`. -/
noncomputable def amplifiedAmplitude {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (A : Finset (Fin N)) (a b : ℝ) (y : Fin N) : ℂ :=
  ∑ z, U y z * (if z ∈ A then (a : ℂ) else (b : ℂ))

/-- With a zero row sum, the marked oracle coefficient sum is minus twice the marked row sum. -/
theorem sum_markedWeight {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (A : Finset (Fin N))
    (y : Fin N) (hrow : ∑ z, U y z = 0) :
    ∑ z, U y z * (if z ∈ A then (-1 : ℂ) else 1) = -2 * ∑ z ∈ A, U y z := by
  have hcomp : ∑ z ∈ Aᶜ, U y z = -∑ z ∈ A, U y z := by
    have h := Finset.sum_add_sum_compl A (fun z => U y z)
    rw [hrow] at h
    simpa using (eq_neg_of_add_eq_zero_right h)
  calc
    ∑ z, U y z * (if z ∈ A then (-1 : ℂ) else 1)
        = (∑ z ∈ A, U y z * (-1)) + ∑ z ∈ Aᶜ, U y z * 1 := by
          rw [← Finset.sum_add_sum_compl A]
          congr 1
          · exact Finset.sum_congr rfl fun z hz => by simp [hz]
          · refine Finset.sum_congr rfl fun z hz => ?_
            simp [Finset.mem_compl.mp hz]
    _ = -∑ z ∈ A, U y z + ∑ z ∈ Aᶜ, U y z := by simp
    _ = -2 * ∑ z ∈ A, U y z := by rw [hcomp]; ring

/-- With a zero row sum, the amplified coefficient sum is the coefficient difference times the
marked row sum. -/
theorem sum_amplifiedWeight {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (A : Finset (Fin N))
    (a b : ℝ) (y : Fin N) (hrow : ∑ z, U y z = 0) :
    ∑ z, U y z * (if z ∈ A then (a : ℂ) else (b : ℂ)) =
      ((a : ℂ) - (b : ℂ)) * ∑ z ∈ A, U y z := by
  have hcomp : ∑ z ∈ Aᶜ, U y z = -∑ z ∈ A, U y z := by
    have h := Finset.sum_add_sum_compl A (fun z => U y z)
    rw [hrow] at h
    simpa using (eq_neg_of_add_eq_zero_right h)
  calc
    ∑ z, U y z * (if z ∈ A then (a : ℂ) else (b : ℂ))
        = (∑ z ∈ A, U y z * (a : ℂ)) + ∑ z ∈ Aᶜ, U y z * (b : ℂ) := by
          rw [← Finset.sum_add_sum_compl A]
          congr 1
          · exact Finset.sum_congr rfl fun z hz => by simp [hz]
          · refine Finset.sum_congr rfl fun z hz => ?_
            simp [Finset.mem_compl.mp hz]
    _ = (a : ℂ) * ∑ z ∈ A, U y z + (b : ℂ) * ∑ z ∈ Aᶜ, U y z := by
          rw [Finset.mul_sum, Finset.mul_sum]
          congr 1
          · exact Finset.sum_congr rfl fun z _ => by ring
          · exact Finset.sum_congr rfl fun z _ => by ring
    _ = ((a : ℂ) - (b : ℂ)) * ∑ z ∈ A, U y z := by rw [hcomp]; ring

/-- The unamplified amplitude is nonzero under the marked-row-sum hypothesis. -/
theorem markedAmplitude_ne_zero {N : ℕ} (hN : 0 < N) (U : Matrix (Fin N) (Fin N) ℂ)
    (A : Finset (Fin N)) (y : Fin N) (hrow : ∑ z, U y z = 0)
    (hmarked : ∑ z ∈ A, U y z ≠ 0) :
    markedAmplitude U A y ≠ 0 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrt : (Real.sqrt (N : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hNpos).ne'
  unfold markedAmplitude
  rw [sum_markedWeight U A y hrow]
  exact mul_ne_zero (inv_ne_zero hsqrt) (mul_ne_zero (by norm_num) hmarked)

/-- The exact amplitude ratio of the two source executions for a matrix at a
label with zero row sum and nonzero marked row sum. -/
theorem general_unitary_amplitude_ratio {N : ℕ} (hN : 0 < N)
    (U : Matrix (Fin N) (Fin N) ℂ) (A : Finset (Fin N)) (a b : ℝ) (y : Fin N)
    (hrow : ∑ z, U y z = 0) (hmarked : ∑ z ∈ A, U y z ≠ 0) :
    amplifiedAmplitude U A a b y / markedAmplitude U A y =
      - (Real.sqrt (N : ℝ) : ℂ) * ((a : ℂ) - (b : ℂ)) / 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrt : (Real.sqrt (N : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hNpos).ne'
  have hden : markedAmplitude U A y ≠ 0 :=
    markedAmplitude_ne_zero hN U A y hrow hmarked
  unfold amplifiedAmplitude markedAmplitude
  rw [sum_amplifiedWeight U A a b y hrow, sum_markedWeight U A y hrow]
  field_simp [hsqrt, hmarked, hden]

/-- The source's scaled marked-minus-unmarked amplitude difference, at a general angle `θ` with
`sin ^ 2 θ = M / 2 ^ n`. This is the identity of [Cornwell2014], Section 2.13, printed p. 54, with
the marked set size `M` and the unmarked size `2 ^ n - M`. -/
theorem sqrt_mul_amplitude_difference (n M k : ℕ) (hM : 0 < M) (hMN : M < 2 ^ n)
    (θ : ℝ) (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hsin : Real.sin θ ^ 2 = (M : ℝ) / (((2 ^ n : ℕ) : ℝ))) :
    Real.sqrt (((2 ^ n : ℕ) : ℝ)) *
        (Real.sin ((2 * (k : ℝ) + 1) * θ) / Real.sqrt (M : ℝ) -
          Real.cos ((2 * (k : ℝ) + 1) * θ) /
            Real.sqrt ((((2 ^ n : ℕ) : ℝ)) - M)) =
      ((((2 ^ n : ℕ) : ℝ)) / (M : ℝ)) * Real.tan θ *
        Real.sin (2 * (k : ℝ) * θ) := by
  set R : ℝ := ((2 ^ n : ℕ) : ℝ) with hR
  have hRpos : (0 : ℝ) < R := by rw [hR]; positivity
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hRMpos : (0 : ℝ) < R - (M : ℝ) := by
    have h : (M : ℝ) < R := by rw [hR]; exact_mod_cast hMN
    linarith
  have hsinR : Real.sin θ ^ 2 = (M : ℝ) / R := by rw [hR]; exact hsin
  have hs : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθpi⟩
  have hc2 : Real.cos θ ^ 2 = (R - (M : ℝ)) / R := by
    have h := Real.sin_sq_add_cos_sq θ
    have hc' : Real.cos θ ^ 2 = 1 - (M : ℝ) / R := by linarith
    rw [hc']
    field_simp [hRpos.ne']
  have hsqrtM : Real.sqrt (M : ℝ) = Real.sqrt R * Real.sin θ := by
    refine (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).mpr ?_
    rw [show Real.sqrt R * Real.sin θ * (Real.sqrt R * Real.sin θ) =
        (Real.sqrt R) ^ 2 * Real.sin θ ^ 2 by ring,
      Real.sq_sqrt hRpos.le, hsinR]
    field_simp [hRpos.ne']
  have hsqrtRM : Real.sqrt (R - (M : ℝ)) = Real.sqrt R * Real.cos θ := by
    refine (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).mpr ?_
    rw [show Real.sqrt R * Real.cos θ * (Real.sqrt R * Real.cos θ) =
        (Real.sqrt R) ^ 2 * Real.cos θ ^ 2 by ring,
      Real.sq_sqrt hRpos.le, hc2]
    field_simp [hRpos.ne']
  have hstep :
      Real.sqrt R *
          (Real.sin ((2 * (k : ℝ) + 1) * θ) / Real.sqrt (M : ℝ) -
            Real.cos ((2 * (k : ℝ) + 1) * θ) / Real.sqrt (R - (M : ℝ))) =
        Real.sin ((2 * (k : ℝ) + 1) * θ) / Real.sin θ -
          Real.cos ((2 * (k : ℝ) + 1) * θ) / Real.cos θ := by
    rw [hsqrtM, hsqrtRM]
    field_simp [hRpos.ne']
  rw [hstep]
  have hφ : (2 * (k : ℝ) + 1) * θ = 2 * (k : ℝ) * θ + θ := by ring
  rw [hφ, Real.sin_add, Real.cos_add, Real.tan_eq_sin_div_cos]
  have hsq := Real.sin_sq_add_cos_sq θ
  have hsinR' : Real.sin θ ^ 2 * R = (M : ℝ) := by
    rw [hsinR]
    field_simp [hRpos.ne']
  field_simp [hs.ne', hc.ne', hMpos.ne', hRpos.ne']
  have hmul : Real.sin (2 * (k : ℝ) * θ) * (Real.sin θ ^ 2 * R) =
      Real.sin (2 * (k : ℝ) * θ) * (M : ℝ) := by rw [hsinR']
  ring_nf at hmul ⊢
  linear_combination (Real.sin ((k : ℝ) * θ * 2) * (M : ℝ)) * hsq - hmul

/-- The probability ratio at the source's floor round count.  The marked set has `M` labels,
`0 < M < 2 ^ n`, and `θ = arcsin (sqrt (M / 2 ^ n))`.  The formula is the one printed in
[Cornwell2014], Section 2.13, printed p. 54. -/
theorem general_unitary_probability_ratio (n M : ℕ) (hM : 0 < M) (hMN : M < 2 ^ n)
    (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (A : Finset (Fin (2 ^ n)))
    (_hcard : A.card = M) (y : Fin (2 ^ n)) (hrow : ∑ z, U y z = 0)
    (hmarked : ∑ z∈A, U y z ≠ 0) :
    let θ : ℝ := generalUnitaryAngle (2 ^ n) M
    let k : ℕ := generalUnitaryRounds (2 ^ n) M
    let a : ℝ := Real.sin ((2 * (k : ℝ) + 1) * θ) / Real.sqrt (M : ℝ)
    let b : ℝ := Real.cos ((2 * (k : ℝ) + 1) * θ) /
      Real.sqrt ((((2 ^ n : ℕ) : ℝ)) - M)
    ‖amplifiedAmplitude U A a b y‖ ^ 2 =
      (1 / 4) * (((((2 ^ n : ℕ) : ℝ)) ^ 2) / (M : ℝ) ^ 2) * (Real.tan θ) ^ 2 *
        (Real.sin (2 * (k : ℝ) * θ)) ^ 2 * ‖markedAmplitude U A y‖ ^ 2 := by
  intro θ k a b
  set R : ℝ := ((2 ^ n : ℕ) : ℝ) with hR
  have hN : 0 < 2 ^ n := by positivity
  have hRpos : (0 : ℝ) < R := by rw [hR]; positivity
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hden : markedAmplitude U A y ≠ 0 :=
    markedAmplitude_ne_zero hN U A y hrow hmarked
  have hratio := general_unitary_amplitude_ratio hN U A a b y hrow hmarked
  have hθdef : θ = generalUnitaryAngle (2 ^ n) M := rfl
  have hsin : Real.sin θ ^ 2 = (M : ℝ) / R := by
    rw [hθdef, generalUnitaryAngle, hR]
    have hMN' : (M : ℝ) < ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast hMN
    rw [Real.sin_arcsin (by nlinarith [Real.sqrt_nonneg ((M : ℝ) / (((2 ^ n : ℕ) : ℝ)))])
      (by
        rw [Real.sqrt_le_one]
        exact (div_le_one (by positivity)).mpr hMN'.le)]
    rw [Real.sq_sqrt (by positivity)]
  have hθpos : 0 < θ := by
    rw [hθdef, generalUnitaryAngle]
    exact Real.arcsin_pos.mpr (Real.sqrt_pos_of_pos (by positivity))
  have hθpi : θ < Real.pi / 2 := by
    rw [hθdef, generalUnitaryAngle]
    exact Real.arcsin_lt_pi_div_two.mpr (by
      have hlt : (M : ℝ) / (((2 ^ n : ℕ) : ℝ)) < 1 := by
        rw [div_lt_one (by positivity)]
        exact_mod_cast hMN
      have hsq : (Real.sqrt ((M : ℝ) / (((2 ^ n : ℕ) : ℝ)))) ^ 2 < 1 := by
        rw [Real.sq_sqrt (by positivity)]
        exact hlt
      exact (pow_lt_one_iff_of_nonneg
        (Real.sqrt_nonneg ((M : ℝ) / (((2 ^ n : ℕ) : ℝ)))) (by norm_num)).mp hsq)
  have hdiff : Real.sqrt R * (a - b) =
      (R / (M : ℝ)) * Real.tan θ * Real.sin (2 * (k : ℝ) * θ) := by
    have h := sqrt_mul_amplitude_difference n M k hM hMN θ hθpos hθpi (by rw [← hR]; exact hsin)
    simpa [a, b, hR] using h
  have hsq : ‖amplifiedAmplitude U A a b y‖ ^ 2 / ‖markedAmplitude U A y‖ ^ 2 =
      R * (a - b) ^ 2 / 4 := by
    have h := congrArg Complex.normSq hratio
    rw [Complex.normSq_div] at h
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h
    rw [h]
    change Complex.normSq (-(Real.sqrt R : ℂ) * ((a : ℂ) - (b : ℂ)) / 2) =
      R * (a - b) ^ 2 / 4
    rw [show (-(Real.sqrt R : ℂ) * ((a : ℂ) - (b : ℂ)) / 2) =
        ((-(Real.sqrt R * (a - b) / 2) : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.normSq_ofReal]
    field_simp
    nlinarith [Real.sq_sqrt hRpos.le]
  have hdiff_sq : (a - b) ^ 2 = (R / (M : ℝ) ^ 2) * (Real.tan θ) ^ 2 *
      (Real.sin (2 * (k : ℝ) * θ)) ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hdiff
    have hsqR : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hRpos.le
    rw [mul_pow, hsqR] at h
    field_simp [hRpos.ne', hMpos.ne'] at h ⊢
    nlinarith [h]
  have hden_sq : ‖markedAmplitude U A y‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hden)
  rw [div_eq_iff hden_sq] at hsq
  rw [hdiff_sq] at hsq
  calc
    ‖amplifiedAmplitude U A a b y‖ ^ 2
        = R * ((R / (M : ℝ) ^ 2) * (Real.tan θ) ^ 2 *
            (Real.sin (2 * (k : ℝ) * θ)) ^ 2) / 4 * ‖markedAmplitude U A y‖ ^ 2 := hsq
    _ = (1 / 4) * (R ^ 2 / (M : ℝ) ^ 2) * (Real.tan θ) ^ 2 *
          (Real.sin (2 * (k : ℝ) * θ)) ^ 2 * ‖markedAmplitude U A y‖ ^ 2 := by ring

/-- In the flat-unitary specialization of [Cornwell2014], Section 2.13, the same amplification
probability ratio as for the Fourier transform holds, with the uniform constant `1/4` outside
all universal quantifiers.  The statement includes the operator-norm unitarity bound, so the
matrix really is an actual unitary, and it is non-vacuous at the two-point Fourier matrix; see
`QatlibTests.AmpTransform14EventAmplification.qft_two_operator_norm`. -/
theorem general_unitary_event_amplification :
    ∃ C > 0, C = 1 / 4 ∧ ∀ (n M : ℕ), 0 < M → M < 2 ^ n →
      ∀ (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ),
        U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ →
        (∀ i j, ‖U i j‖ = (Real.sqrt (((2 ^ n : ℕ) : ℝ)))⁻¹) →
        ∀ (A : Finset (Fin (2 ^ n))), A.card = M →
        ∀ (y : Fin (2 ^ n)), (∑ z, U y z = 0) → (∑ z∈A, U y z ≠ 0) →
        let θ : ℝ := generalUnitaryAngle (2 ^ n) M
        let k : ℕ := generalUnitaryRounds (2 ^ n) M
        let a : ℝ := Real.sin ((2 * (k : ℝ) + 1) * θ) / Real.sqrt (M : ℝ)
        let b : ℝ := Real.cos ((2 * (k : ℝ) + 1) * θ) /
          Real.sqrt ((((2 ^ n : ℕ) : ℝ)) - M)
        ‖U‖ ≤ 1 ∧
          ‖amplifiedAmplitude U A a b y‖ ^ 2 =
            C * (((((2 ^ n : ℕ) : ℝ)) ^ 2) / (M : ℝ) ^ 2) * (Real.tan θ) ^ 2 *
              (Real.sin (2 * (k : ℝ) * θ)) ^ 2 * ‖markedAmplitude U A y‖ ^ 2 := by
  refine ⟨1 / 4, by norm_num, rfl, ?_⟩
  intro n M hM hMN U hU _hflat A hcard y hrow hmarked θ k a b
  exact ⟨Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_unitary_le_one hU,
    general_unitary_probability_ratio n M hM hMN U A hcard y hrow hmarked⟩

end Qatlib.Papers.AmpTransform14.GeneralUnitary
