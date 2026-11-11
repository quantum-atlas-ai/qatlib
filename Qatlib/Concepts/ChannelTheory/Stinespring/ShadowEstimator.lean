/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState

/-!
# Single-qubit Pauli shadow estimator

This module defines the Pauli measurement projectors and the estimator `PauliShadow`, equal to
three times the observed projector minus the identity. It proves the Bloch reconstruction
formula and shows that averaging this estimator over uniformly chosen Pauli axes and
Born-distributed outcomes recovers the input density matrix [HuangKuengPreskill2020].

## Main statements

* `pauliProjector_sum`: the two outcome projectors sum to the identity.
* `bloch_reconstruction`: a qubit density operator is reconstructed from its three Pauli
  expectations.
* `pauliShadow_unbiased`: the Pauli shadow estimator is unbiased.

## References

* [Huang et al., 2020][HuangKuengPreskill2020]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Concepts.ChannelTheory.Stinespring

open scoped ComplexOrder

set_option maxHeartbeats 4000000

/-- The Pauli X matrix, which exchanges the two computational basis vectors. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli Y matrix with off-diagonal entries `-Complex.I` and `Complex.I`. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli Z matrix with diagonal entries one and minus one. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Pauli matrix indexed by an axis in `Fin 3`, in X, Y, Z order. -/
def pauliMatrix (a : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  if a = 0 then pauliX else if a = 1 then pauliY else pauliZ

/-- Axis zero selects the Pauli X matrix. -/
@[simp] theorem pauliMatrix_zero : pauliMatrix 0 = pauliX := rfl

/-- Axis one selects the Pauli Y matrix. -/
@[simp] theorem pauliMatrix_one : pauliMatrix 1 = pauliY := rfl

/-- Axis two selects the Pauli Z matrix. -/
@[simp] theorem pauliMatrix_two : pauliMatrix 2 = pauliZ := rfl

/-- The Pauli-axis outcome projector, using eigenvalue one for `true` and minus one for `false`. -/
noncomputable def PauliProjector (a : Fin 3) (b : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 + (if b then 1 else -1 : ℂ) • pauliMatrix a)

/-- The single-qubit Pauli shadow estimator `3 • PauliProjector a b - 1`
[HuangKuengPreskill2020]. -/
noncomputable def PauliShadow (b : Bool) (a : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  3 • PauliProjector a b - 1

/-- The real part of the trace of the selected Pauli matrix multiplied by `ρ`. -/
noncomputable def pauliExpectation (a : Fin 3) (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (Matrix.trace (pauliMatrix a * ρ)).re

/-- A finite sum over `Bool` is the sum of its values at `false` and `true`. -/
theorem sum_bool {α : Type*} [AddCommMonoid α] (f : Bool → α) :
    ∑ b : Bool, f b = f false + f true := by
  rw [show (Finset.univ : Finset Bool) = {false, true} from by decide]
  exact Finset.sum_pair (by decide)

/-- The two outcome projectors for a fixed Pauli axis sum to the identity. -/
theorem pauliProjector_sum (a : Fin 3) : ∑ b : Bool, PauliProjector a b = 1 := by
  rw [sum_bool]
  simp only [PauliProjector, eq_self_iff_true, if_true, Bool.false_eq_true, if_false]
  module

/-- The trace of `pauliX * ρ` is the sum of the two off-diagonal entries of `ρ`. -/
theorem trace_pauliX_mul (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (pauliX * ρ) = ρ 0 1 + ρ 1 0 := by
  rw [Matrix.trace_fin_two]
  simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The trace of `pauliY * ρ` is `Complex.I` times the upper off-diagonal entry minus
`Complex.I` times the lower one. -/
theorem trace_pauliY_mul (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (pauliY * ρ) = Complex.I * ρ 0 1 - Complex.I * ρ 1 0 := by
  rw [Matrix.trace_fin_two]
  simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The trace of `pauliZ * ρ` is the difference of the diagonal entries of `ρ`. -/
theorem trace_pauliZ_mul (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (pauliZ * ρ) = ρ 0 0 - ρ 1 1 := by
  rw [Matrix.trace_fin_two]
  simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- A qubit density operator equals one half of the sum of the identity and its Pauli expansion,
whose coefficients are its real Pauli expectations. -/
theorem bloch_reconstruction (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : IsDensityOperator ρ) :
    ρ = (1 / 2 : ℂ) • (1 + ∑ a : Fin 3, (pauliExpectation a ρ : ℂ) • pauliMatrix a) := by
  have hherm : ρ.IsHermitian := hρ.1.isHermitian
  have h10 : ρ 1 0 = starRingEnd ℂ (ρ 0 1) := by
    have h2 := congrFun (congrFun hherm 1) 0
    rw [Matrix.conjTranspose_apply] at h2
    exact h2.symm
  have him00 : (ρ 0 0).im = 0 := by
    have h2 := congrFun (congrFun hherm 0) 0
    rw [Matrix.conjTranspose_apply] at h2
    exact Complex.conj_eq_iff_im.mp h2
  have him11 : (ρ 1 1).im = 0 := by
    have h2 := congrFun (congrFun hherm 1) 1
    rw [Matrix.conjTranspose_apply] at h2
    exact Complex.conj_eq_iff_im.mp h2
  have htr : (ρ 0 0).re + (ρ 1 1).re = 1 := by
    have h2 : Matrix.trace ρ = 1 := hρ.2
    rw [Matrix.trace_fin_two] at h2
    have h3 := congrArg Complex.re h2
    simp only [Complex.add_re, Complex.one_re] at h3
    exact h3
  ext i j
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) from by norm_num [Complex.ofReal_div]]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sum_apply, Fin.sum_univ_three,
      pauliMatrix_zero, pauliMatrix_one, pauliMatrix_two, pauliExpectation,
      trace_pauliX_mul, trace_pauliY_mul, trace_pauliZ_mul, smul_eq_mul] <;>
    simp [h10, pauliX, pauliY, pauliZ, Matrix.one_apply] <;>
    refine Complex.ext_iff.mpr ⟨?_, ?_⟩ <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im, Fin.isValue] <;>
    norm_num <;> linarith [htr, him00, him11]

/-- For a trace-one matrix, the outcome-weighted shadow sum at a fixed axis is one half of the
identity plus three halves of the corresponding Pauli expectation term. -/
theorem pauliShadow_sum_axis (a : Fin 3) (ρ : Matrix (Fin 2) (Fin 2) ℂ)
    (hρtr : Matrix.trace ρ = 1) :
    ∑ b : Bool, ((Matrix.trace (PauliProjector a b * ρ)).re : ℂ) • PauliShadow b a
      = (1 / 2 : ℂ) • (1 + (3 : ℂ) • (pauliExpectation a ρ : ℂ) • pauliMatrix a) := by
  set w : ℂ := Matrix.trace (pauliMatrix a * ρ) with hw

  have htrP : ∀ b : Bool, Matrix.trace (PauliProjector a b * ρ)
      = (1 / 2 : ℂ) * (1 + (if b then 1 else -1 : ℂ) * w) := by
    intro b
    calc Matrix.trace (PauliProjector a b * ρ)
        = Matrix.trace ((1 / 2 : ℂ) •
            ((1 + (if b then 1 else -1 : ℂ) • pauliMatrix a) * ρ)) := by
          rw [PauliProjector, Matrix.smul_mul]
      _ = (1 / 2 : ℂ) * (1 + (if b then 1 else -1 : ℂ) * w) := by
          rw [Matrix.trace_smul, Matrix.add_mul, Matrix.trace_add, Matrix.one_mul, hρtr,
            Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← hw, smul_eq_mul]

  have ht1 : ((Matrix.trace (PauliProjector a true * ρ)).re : ℂ)
      = (((1 / 2 : ℂ) * (1 + w)).re : ℂ) := by
    rw [htrP true]
    simp
  have ht0 : ((Matrix.trace (PauliProjector a false * ρ)).re : ℂ)
      = (((1 / 2 : ℂ) * (1 - w)).re : ℂ) := by
    rw [htrP false]
    simp [sub_eq_add_neg]

  have hsum : (((1 / 2 : ℂ) * (1 - w)).re : ℂ) + (((1 / 2 : ℂ) * (1 + w)).re : ℂ)
      = 1 := by
    rw [← Complex.ofReal_add, ← Complex.add_re,
      show (1 / 2 : ℂ) * (1 - w) + (1 / 2 : ℂ) * (1 + w) = 1 from by ring]
    simp

  have hdiff : (((1 / 2 : ℂ) * (1 + w)).re : ℂ) - (((1 / 2 : ℂ) * (1 - w)).re : ℂ)
      = (w.re : ℂ) := by
    rw [← Complex.ofReal_sub, ← Complex.sub_re,
      show (1 / 2 : ℂ) * (1 + w) - (1 / 2 : ℂ) * (1 - w) = w from by ring]

  have hmod : ∀ t₁ t₂ : ℂ, ∀ σ : Matrix (Fin 2) (Fin 2) ℂ,
      t₁ • (3 • ((1 / 2 : ℂ) • (1 + (-1 : ℂ) • σ)) - 1)
        + t₂ • (3 • ((1 / 2 : ℂ) • (1 + (1 : ℂ) • σ)) - 1)
      = ((t₁ + t₂) / 2) • 1 + ((3 / 2 : ℂ) * (t₂ - t₁)) • σ := by
    intro t₁ t₂ σ
    module
  have hpe : (pauliExpectation a ρ : ℂ) = (w.re : ℂ) := rfl
  rw [sum_bool, ht0, ht1]
  simp only [PauliShadow, PauliProjector, Bool.false_eq_true, if_false, if_true]
  rw [hmod, hsum, hdiff, hpe]
  module

/-- Averaging `PauliShadow` over the three Pauli axes and their Born outcome probabilities
recovers the qubit density operator [HuangKuengPreskill2020]. -/
theorem pauliShadow_unbiased (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : IsDensityOperator ρ) :
    (1 / 3 : ℂ) • ∑ a : Fin 3, ∑ b : Bool,
      ((Matrix.trace (PauliProjector a b * ρ)).re : ℂ) • PauliShadow b a = ρ := by
  calc (1 / 3 : ℂ) • ∑ a : Fin 3, ∑ b : Bool,
        ((Matrix.trace (PauliProjector a b * ρ)).re : ℂ) • PauliShadow b a
      = (1 / 3 : ℂ) • ∑ a : Fin 3,
          (1 / 2 : ℂ) • (1 + (3 : ℂ) • (pauliExpectation a ρ : ℂ) • pauliMatrix a) := by
        congr 1
        exact Finset.sum_congr rfl fun a _ => pauliShadow_sum_axis a ρ hρ.2
    _ = (1 / 2 : ℂ) • (1 + ∑ a : Fin 3, (pauliExpectation a ρ : ℂ) • pauliMatrix a) := by
        have step : ∀ a : Fin 3,
            (1 / 2 : ℂ) • (1 + (3 : ℂ) • (pauliExpectation a ρ : ℂ) • pauliMatrix a)
              = (1 / 2 : ℂ) • 1
                + ((3 / 2 : ℂ) • ((pauliExpectation a ρ : ℂ) • pauliMatrix a)) :=
          fun a => by module
        rw [Finset.sum_congr rfl fun a _ => step a, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Finset.smul_sum]
        module
    _ = ρ := (bloch_reconstruction ρ hρ).symm

end Qatlib.Concepts.ChannelTheory.Stinespring
