/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.PauliClifford.ExactRank.MeasuredPauliShadows
open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Matrix
open scoped ComplexOrder

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

def tetraSigns (a : Fin 4) (j : Fin 3) : ℝ :=
  if a = 0 then 1
  else if a = 1 then (if j = 0 then 1 else -1)
  else if a = 2 then (if j = 1 then 1 else -1)
  else if j = 2 then 1 else -1

@[simp] theorem tetraSigns_zero (j : Fin 3) : tetraSigns 0 j = 1 := rfl

@[simp] theorem tetraSigns_one (j : Fin 3) : tetraSigns 1 j = if j = 0 then 1 else -1 := rfl

@[simp] theorem tetraSigns_two (j : Fin 3) : tetraSigns 2 j = if j = 1 then 1 else -1 := rfl

@[simp] theorem tetraSigns_three (j : Fin 3) : tetraSigns 3 j = if j = 2 then 1 else -1 := rfl

theorem tetraSigns_row_sq (a : Fin 4) : ∑ j : Fin 3, (tetraSigns a j) ^ 2 = 3 := by
  fin_cases a <;> simp

theorem tetraSigns_col_sum (j : Fin 3) : ∑ a : Fin 4, tetraSigns a j = 0 := by
  fin_cases j <;> simp [Fin.sum_univ_four]

theorem tetraSigns_frame (j k : Fin 3) :
    ∑ a : Fin 4, tetraSigns a j * tetraSigns a k = if j = k then 4 else 0 := by
  fin_cases j <;> fin_cases k <;> simp [Fin.sum_univ_four] <;> try norm_num

noncomputable def tetraSignPauli (a : Fin 4) : Operator 2 :=
  ∑ j : Fin 3, ((tetraSigns a j : ℝ) : ℂ) • pauliMatrix j

theorem tetraSignPauli_conjTranspose (a : Fin 4) :
    (tetraSignPauli a)ᴴ = tetraSignPauli a := by
  rw [tetraSignPauli, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_smul,
    show star ((tetraSigns a j : ℝ) : ℂ) = ((tetraSigns a j : ℝ) : ℂ) from by
      simp [Complex.conj_ofReal], pauliMatrix_conjTranspose]

theorem tetraSignPauli_mul_self (a : Fin 4) :
    tetraSignPauli a * tetraSignPauli a
      = ((∑ j : Fin 3, (tetraSigns a j) ^ 2 : ℝ) : ℂ) • (1 : Operator 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> fin_cases a <;>
    simp [tetraSignPauli, Matrix.mul_apply, Matrix.smul_apply,
      smul_eq_mul, Fin.sum_univ_three, pauliX, pauliY, pauliZ,
      Matrix.of_apply, apply_ite] <;>
    ring_nf <;>
    norm_num [Complex.I_mul_I]

noncomputable def tetraSigmaComb (a : Fin 4) : Operator 2 :=
  ∑ j : Fin 3, ((tetraSigns a j / Real.sqrt 3 : ℝ) : ℂ) • pauliMatrix j

theorem tetraSigmaComb_eq (a : Fin 4) :
    tetraSigmaComb a = ((Real.sqrt 3 : ℝ) : ℂ)⁻¹ • tetraSignPauli a := by
  have hscal : ∀ n : ℝ, (((n / Real.sqrt 3 : ℝ) : ℂ))
      = ((Real.sqrt 3 : ℝ) : ℂ)⁻¹ * ((n : ℝ) : ℂ) := by
    intro n
    rw [Complex.ofReal_div]
    ring
  simp only [tetraSigmaComb, tetraSignPauli, hscal]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]

theorem tetraSigmaComb_conjTranspose (a : Fin 4) :
    (tetraSigmaComb a)ᴴ = tetraSigmaComb a := by
  rw [tetraSigmaComb_eq, Matrix.conjTranspose_smul,
    show star (((Real.sqrt 3 : ℝ) : ℂ)⁻¹) = ((Real.sqrt 3 : ℝ) : ℂ)⁻¹ from by simp,
    tetraSignPauli_conjTranspose]

theorem tetraSigmaComb_mul_self (a : Fin 4) : tetraSigmaComb a * tetraSigmaComb a = 1 := by
  have hsqrt : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = ((3 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  rw [tetraSigmaComb_eq, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    tetraSignPauli_mul_self, tetraSigns_row_sq a, smul_smul]
  have hscal : ((Real.sqrt 3 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 3 : ℝ) : ℂ)⁻¹ * ((3 : ℝ) : ℂ) = 1 := by
    have hne : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3)
    calc ((Real.sqrt 3 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 3 : ℝ) : ℂ)⁻¹ * ((3 : ℝ) : ℂ)
        = ((Real.sqrt 3 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 3 : ℝ) : ℂ)⁻¹
            * (((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ)) := by rw [hsqrt]
      _ = (((Real.sqrt 3 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 3 : ℝ) : ℂ))
            * (((Real.sqrt 3 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 3 : ℝ) : ℂ)) := by ring
      _ = 1 := by rw [inv_mul_cancel₀ hne, one_mul]
  rw [hscal, one_smul]

noncomputable def tetraProjector (a : Fin 4) : Operator 2 :=
  (1 / 2 : ℂ) • (1 + tetraSigmaComb a)

noncomputable def tetraKraus (a : Fin 4) : Operator 2 :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • tetraProjector a

noncomputable def tetraSnapshot (a : Fin 4) : Operator 2 :=
  (3 : ℂ) • tetraProjector a - 1

theorem tetraProjector_conjTranspose (a : Fin 4) :
    (tetraProjector a)ᴴ = tetraProjector a := by
  rw [tetraProjector, Matrix.conjTranspose_smul,
    show star ((1 : ℂ) / 2) = 1 / 2 from by norm_num,
    Matrix.conjTranspose_add, Matrix.conjTranspose_one, tetraSigmaComb_conjTranspose]

theorem tetraProjector_mul_self (a : Fin 4) :
    tetraProjector a * tetraProjector a = tetraProjector a := by
  have hS := tetraSigmaComb_mul_self a
  rw [tetraProjector, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hcore : (1 + tetraSigmaComb a) * (1 + tetraSigmaComb a)
      = (2 : ℂ) • (1 + tetraSigmaComb a) := by
    have e1 : (1 + tetraSigmaComb a) * (1 + tetraSigmaComb a)
        = 1 + tetraSigmaComb a + (tetraSigmaComb a + tetraSigmaComb a * tetraSigmaComb a) := by
      rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one]
    rw [e1, hS]
    module
  rw [hcore]
  module

theorem trace_pauliMatrix_local (j : Fin 3) : Matrix.trace (pauliMatrix j) = 0 := by
  fin_cases j <;> simp [pauliX, pauliY, pauliZ, Matrix.trace_fin_two]

theorem trace_one_two : Matrix.trace (1 : Operator 2) = 2 := by
  rw [Matrix.trace_one, Fintype.card_fin]
  norm_num

theorem tetraProjector_trace (a : Fin 4) : Matrix.trace (tetraProjector a) = 1 := by
  have hsig : Matrix.trace (tetraSigmaComb a) = 0 := by
    rw [tetraSigmaComb, Matrix.trace_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.trace_smul, trace_pauliMatrix_local, smul_zero]
  rw [tetraProjector, Matrix.trace_smul, smul_eq_mul, Matrix.trace_add, hsig, add_zero,
    trace_one_two]
  norm_num

theorem tetraSignPauli_sum_zero : ∑ a : Fin 4, tetraSignPauli a = 0 := by
  simp only [tetraSignPauli]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [← Finset.sum_smul, ← Complex.ofReal_sum, tetraSigns_col_sum k]
  norm_num

theorem tetraProjector_sum : ∑ a : Fin 4, tetraProjector a = (2 : ℂ) • (1 : Operator 2) := by
  have hsigma : ∑ a : Fin 4, tetraSigmaComb a = 0 := by
    rw [Finset.sum_congr rfl fun a _ => tetraSigmaComb_eq a, ← Finset.smul_sum,
      tetraSignPauli_sum_zero, smul_zero]
  calc ∑ a : Fin 4, tetraProjector a
      = ∑ a : Fin 4, (1 / 2 : ℂ) • (1 + tetraSigmaComb a) := rfl
    _ = (1 / 2 : ℂ) • (∑ a : Fin 4, (1 + tetraSigmaComb a)) := by rw [← Finset.smul_sum]
    _ = (1 / 2 : ℂ) • ((∑ a : Fin 4, (1 : Operator 2)) + ∑ a : Fin 4, tetraSigmaComb a) := by
        rw [Finset.sum_add_distrib]
    _ = (2 : ℂ) • (1 : Operator 2) := by
        rw [hsigma, add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          ← Nat.cast_smul_eq_nsmul (R := ℂ), Nat.cast_ofNat]
        module

theorem tetraKraus_conjTranspose (a : Fin 4) : (tetraKraus a)ᴴ = tetraKraus a := by
  rw [tetraKraus, Matrix.conjTranspose_smul,
    show star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ from by simp,
    tetraProjector_conjTranspose]

theorem tetraKraus_conj_mul (a : Fin 4) :
    (tetraKraus a)ᴴ * tetraKraus a = (1 / 2 : ℂ) • tetraProjector a := by
  rw [tetraKraus_conjTranspose]
  show (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • tetraProjector a)
      * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • tetraProjector a) = (1 / 2 : ℂ) • tetraProjector a
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, tetraProjector_mul_self,
    show (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ : ℂ) = (1 : ℂ) / 2 from
      inv_sqrt2_mul_self.trans (by norm_num)]

theorem tetraKraus_complete : ∑ a : Fin 4, (tetraKraus a)ᴴ * tetraKraus a = 1 := by
  calc ∑ a : Fin 4, (tetraKraus a)ᴴ * tetraKraus a
      = ∑ a : Fin 4, (1 / 2 : ℂ) • tetraProjector a :=
        Finset.sum_congr rfl fun a _ => tetraKraus_conj_mul a
    _ = (1 / 2 : ℂ) • ∑ a : Fin 4, tetraProjector a := by rw [← Finset.smul_sum]
    _ = (1 / 2 : ℂ) • ((2 : ℂ) • (1 : Operator 2)) := by rw [tetraProjector_sum]
    _ = 1 := by module

theorem tetrahedral_actual_projectors_and_kraus_complete :
    (∀ a : Fin 4, (∑ j : Fin 3, (tetraSigns a j) ^ 2) = 3) ∧
      (∀ a, tetraProjector a
        = (1 / 2 : ℂ) • (1 + ∑ j : Fin 3, ((tetraSigns a j / Real.sqrt 3) : ℂ) • pauliMatrix j)) ∧
      (∀ a, (tetraProjector a)ᴴ = tetraProjector a ∧
        tetraProjector a * tetraProjector a = tetraProjector a) ∧
      (∀ a, tetraKraus a = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • tetraProjector a) ∧
      ∑ a : Fin 4, (tetraKraus a)ᴴ * tetraKraus a = 1 :=
  ⟨tetraSigns_row_sq, fun a => by
      simp only [tetraProjector, tetraSigmaComb, Complex.ofReal_div],
    fun a => ⟨tetraProjector_conjTranspose a, tetraProjector_mul_self a⟩, fun _ => rfl,
    tetraKraus_complete⟩

noncomputable def tetraInstrument : Instrument (Fin 4) 2 2 :=
  Instrument.ofKraus tetraKraus tetraKraus_complete

noncomputable def tetraRecordLaw (ρ : Operator 2) (hρ : IsDensityOperator ρ) :
    FinDist (Fin 4) where
  prob a := instrumentProb tetraInstrument ρ a
  nonneg a := instrumentProb_nonneg tetraInstrument hρ.1 a
  sum_one := sum_instrumentProb_isDensityOperator tetraInstrument hρ

theorem tetrahedral_actual_record_born_law (ρ : Operator 2) (hρ : IsDensityOperator ρ)
    (a : Fin 4) :
    tetraInstrument.branch a ρ = tetraKraus a * ρ * (tetraKraus a)ᴴ ∧
      (tetraRecordLaw ρ hρ).prob a = instrumentProb tetraInstrument ρ a ∧
      (tetraRecordLaw ρ hρ).prob a = (Matrix.trace (tetraProjector a * ρ)).re / 2 := by
  have htr : Matrix.trace (tetraKraus a * ρ * (tetraKraus a)ᴴ)
      = (1 / 2 : ℂ) * Matrix.trace (tetraProjector a * ρ) := by
    rw [tetraKraus, Matrix.conjTranspose_smul,
      show star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ from by simp,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
      smul_smul, tetraProjector_conjTranspose,
      show (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ : ℂ) = (2 : ℂ)⁻¹ from
        inv_sqrt2_mul_self, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc,
      Matrix.trace_mul_cycle', Matrix.trace_mul_cycle', tetraProjector_mul_self a,
      Matrix.trace_mul_comm]; norm_num
  refine ⟨rfl, rfl, ?_⟩
  show (Matrix.trace (tetraInstrument.branch a ρ)).re = _
  rw [show tetraInstrument.branch a ρ = tetraKraus a * ρ * (tetraKraus a)ᴴ from rfl, htr,
    show ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) from by norm_num [Complex.ofReal_div]]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem tetrahedral_prob_sum (ρ : Operator 2) (hρ : IsDensityOperator ρ) :
    ∑ a : Fin 4, (((tetraRecordLaw ρ hρ).prob a : ℝ) : ℂ) = 1 := by
  rw [Finset.sum_congr rfl fun a _ => show (((tetraRecordLaw ρ hρ).prob a : ℝ) : ℂ)
      = ((((Matrix.trace (tetraProjector a * ρ)).re / 2 : ℝ)) : ℂ) from by
      rw [(tetrahedral_actual_record_born_law ρ hρ a).2.2]]
  push_cast [Complex.ofReal_div]
  rw [← Finset.sum_div, ← Complex.ofReal_sum, ← Complex.re_sum]
  have htotal : ∑ a : Fin 4, Matrix.trace (tetraProjector a * ρ)
      = (2 : ℂ) * Matrix.trace ρ := by
    rw [← Matrix.trace_sum, ← Finset.sum_mul, tetraProjector_sum, Matrix.smul_mul,
      Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]
  rw [htotal, hρ.2]
  norm_num [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re]

theorem tetrahedral_trace_col (ρ : Operator 2) (j : Fin 3) :
    ∑ a : Fin 4, (Matrix.trace (tetraProjector a * ρ)).re * tetraSigns a j
      = (2 / Real.sqrt 3) * (Matrix.trace (pauliMatrix j * ρ)).re := by
  have hcol : ∀ a : Fin 4, ((Matrix.trace (tetraProjector a * ρ)).re * tetraSigns a j : ℝ)
      = (Matrix.trace (tetraProjector a * ρ) * ((tetraSigns a j : ℝ) : ℂ)).re := by
    intro a
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    simp
  rw [Finset.sum_congr rfl fun a _ => hcol a, ← Complex.re_sum]
  have hrowC : ∑ a : Fin 4, Matrix.trace (tetraProjector a * ρ) * ((tetraSigns a j : ℝ) : ℂ)
      = ((2 / Real.sqrt 3 : ℝ) : ℂ) • Matrix.trace (pauliMatrix j * ρ) := by
    have hexp : ∀ a : Fin 4, Matrix.trace (tetraProjector a * ρ)
        = (1 / 2 : ℂ) * (Matrix.trace ρ + ((Real.sqrt 3 : ℝ) : ℂ)⁻¹
            * ∑ k : Fin 3, ((tetraSigns a k : ℝ) : ℂ) * Matrix.trace (pauliMatrix k * ρ)) := by
      intro a
      rw [tetraProjector, tetraSigmaComb_eq, Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul,
        Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.trace_add,
        Matrix.trace_smul, smul_eq_mul, tetraSignPauli, Finset.sum_mul,
        Matrix.trace_sum, Finset.sum_congr rfl fun k _ => (by
          rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul])]
    have hsplit : ∀ a : Fin 4,
        Matrix.trace (tetraProjector a * ρ) * ((tetraSigns a j : ℝ) : ℂ)
          = ((1 / 2 : ℝ) : ℂ) * ((tetraSigns a j : ℝ) : ℂ) * Matrix.trace ρ
            + ((1 / (2 * Real.sqrt 3) : ℝ) : ℂ) * (∑ k : Fin 3, ((tetraSigns a k : ℝ) : ℂ)
                * Matrix.trace (pauliMatrix k * ρ)) * ((tetraSigns a j : ℝ) : ℂ) := by
      intro a
      rw [hexp a]
      push_cast [Complex.ofReal_div, Complex.ofReal_inv, Complex.ofReal_mul]
      ring
    rw [Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_add_distrib]
    have ht1 : ∑ a : Fin 4, ((1 / 2 : ℝ) : ℂ) * ((tetraSigns a j : ℝ) : ℂ) * Matrix.trace ρ
        = 0 := by
      fin_cases j <;> simp [Fin.sum_univ_four]
    have hinner : ∀ a : Fin 4,
        ((1 / (2 * Real.sqrt 3) : ℝ) : ℂ) * (∑ k : Fin 3, ((tetraSigns a k : ℝ) : ℂ)
            * Matrix.trace (pauliMatrix k * ρ)) * ((tetraSigns a j : ℝ) : ℂ)
        = ∑ k : Fin 3, ((1 / (2 * Real.sqrt 3) : ℝ) : ℂ)
            * (((tetraSigns a k * tetraSigns a j : ℝ) : ℂ) * Matrix.trace (pauliMatrix k * ρ)) := by
      intro a
      rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_right_comm, ← Complex.ofReal_mul]
    have hne : (Real.sqrt 3 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (show (0 : ℝ) < 3 by norm_num)
    have hne2 : (2 * Real.sqrt 3 : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hne
    have hscal4 : ((1 / (2 * Real.sqrt 3) : ℝ) : ℂ) * ((4 : ℝ) : ℂ)
        = ((2 / Real.sqrt 3 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Complex.ofReal_inj, mul_comm, ← mul_div_assoc,
        div_eq_div_iff hne2 hne]
      ring
    have hcollect : ∀ k : Fin 3, (∑ x : Fin 4, ((1 / (2 * Real.sqrt 3) : ℝ) : ℂ)
        * (((tetraSigns x k * tetraSigns x j : ℝ) : ℂ) * Matrix.trace (pauliMatrix k * ρ)))
      = ((1 / (2 * Real.sqrt 3) : ℝ) : ℂ) * (((∑ x : Fin 4,
            (tetraSigns x k * tetraSigns x j : ℝ) : ℝ) : ℂ) * Matrix.trace (pauliMatrix k * ρ)) := by
      intro k
      rw [Finset.sum_congr rfl fun x _ => show (((1 / (2 * Real.sqrt 3) : ℝ) : ℂ)
            * (((tetraSigns x k * tetraSigns x j : ℝ) : ℂ) * Matrix.trace (pauliMatrix k * ρ)))
          = (((1 / (2 * Real.sqrt 3) : ℝ) : ℂ) * ((tetraSigns x k * tetraSigns x j : ℝ) : ℂ))
              * Matrix.trace (pauliMatrix k * ρ) from by ring,
        ← Finset.sum_mul, ← Finset.mul_sum, ← Complex.ofReal_sum, mul_assoc]
    rw [ht1, zero_add, Finset.sum_congr rfl fun a _ => hinner a, Finset.sum_comm,
      Finset.sum_congr rfl fun k _ => hcollect k]
    have hsplitrhs : ((2 / Real.sqrt 3 : ℝ) : ℂ) • Matrix.trace (pauliMatrix j * ρ)
        = ∑ k : Fin 3, if k = j
            then ((2 / Real.sqrt 3 : ℝ) : ℂ) • Matrix.trace (pauliMatrix k * ρ) else 0 := by
      have h0 : ∀ k : Fin 3, k ≠ j → ((if k = j then ((2 / Real.sqrt 3 : ℝ) : ℂ)
            • Matrix.trace (pauliMatrix k * ρ) else 0) = 0) := by
        intro k hkj
        rw [if_neg hkj]
      simp only [Finset.sum_eq_single j (fun k _ hkj => h0 k hkj)
        (fun h => (h (Finset.mem_univ _)).elim), if_true]
    rw [hsplitrhs]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hkj : k = j
    · rw [if_pos hkj, tetraSigns_frame k j, if_pos hkj, smul_eq_mul, ← mul_assoc, hscal4]
    · rw [if_neg hkj, tetraSigns_frame k j, if_neg hkj]
      simp
  rw [hrowC]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem tetrahedral_weighted_effect_sum (ρ : Operator 2) (hρ : IsDensityOperator ρ) :
    ∑ a : Fin 4, ((Matrix.trace (tetraProjector a * ρ)).re : ℂ) • tetraProjector a
      = (1 : ℂ) • (1 : Operator 2)
        + (1 / 3 : ℂ) • ∑ j : Fin 3, ((pauliExpectation j ρ : ℝ) : ℂ) • pauliMatrix j := by
  simp only [pauliExpectation]
  have hsumx : ∑ a : Fin 4, (Matrix.trace (tetraProjector a * ρ)).re = 2 := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, tetraProjector_sum,
      Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul, hρ.2]
    norm_num
  have hcolC : ∀ j : Fin 3,
      ∑ a : Fin 4, ((Matrix.trace (tetraProjector a * ρ)).re : ℂ)
          * ((tetraSigns a j / Real.sqrt 3 : ℝ) : ℂ)
      = ((((2 / 3) * (Matrix.trace (pauliMatrix j * ρ)).re : ℝ)) : ℂ) := by
    intro j
    have hsplitc : ∀ a : Fin 4, ((Matrix.trace (tetraProjector a * ρ)).re : ℂ)
        * ((tetraSigns a j / Real.sqrt 3 : ℝ) : ℂ)
        = ((((Matrix.trace (tetraProjector a * ρ)).re * tetraSigns a j / Real.sqrt 3 : ℝ)) : ℂ) := by
      intro a
      rw [Complex.ofReal_div, Complex.ofReal_div, Complex.ofReal_mul]
      ring
    have hsqrt3 : Real.sqrt 3 * Real.sqrt 3 = 3 :=
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    rw [Finset.sum_congr rfl fun a _ => hsplitc a, ← Complex.ofReal_sum,
      ← Finset.sum_div, tetrahedral_trace_col ρ j, Complex.ofReal_inj, mul_comm,
      mul_div_assoc, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc,
      ← mul_inv, hsqrt3, mul_comm]
  have hsplit : ∀ a : Fin 4,
      ((Matrix.trace (tetraProjector a * ρ)).re : ℂ) • tetraProjector a
        = ((1 / 2 : ℂ) * ((Matrix.trace (tetraProjector a * ρ)).re : ℂ)) • (1 : Operator 2)
          + ∑ j : Fin 3, (((1 / 2 : ℂ) * ((Matrix.trace (tetraProjector a * ρ)).re : ℂ))
              * ((tetraSigns a j / Real.sqrt 3 : ℝ) : ℂ)) • pauliMatrix j := by
    intro a
    rw [tetraProjector, smul_smul, mul_comm, smul_add, tetraSigmaComb, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul]
  rw [Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_add_distrib]
  have hid : ∑ a : Fin 4, ((1 / 2 : ℂ) * ((Matrix.trace (tetraProjector a * ρ)).re : ℂ)) = 1 := by
    rw [← Finset.mul_sum, ← Complex.ofReal_sum, hsumx]
    norm_num [show ((2 : ℝ) : ℂ) = (2 : ℂ) from rfl]
  rw [← Finset.sum_smul, hid, Finset.smul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hfac : ∀ a : Fin 4, (((1 / 2 : ℂ) * ((Matrix.trace (tetraProjector a * ρ)).re : ℂ))
        * ((tetraSigns a j / Real.sqrt 3 : ℝ) : ℂ)) • pauliMatrix j
      = (1 / 2 : ℂ) • ((((Matrix.trace (tetraProjector a * ρ)).re : ℂ)
          * ((tetraSigns a j / Real.sqrt 3 : ℝ) : ℂ)) • pauliMatrix j) := by
    intro a
    rw [smul_smul]
    exact congrArg (fun z : ℂ => z • pauliMatrix j) (by ring)
  rw [Finset.sum_congr rfl fun a _ => hfac a, ← Finset.smul_sum, ← Finset.sum_smul,
    hcolC j, smul_smul, smul_smul, Complex.ofReal_mul, Complex.ofReal_div,
    show ((2 : ℝ) : ℂ) = (2 : ℂ) from rfl, show ((3 : ℝ) : ℂ) = (3 : ℂ) from rfl]
  congr 1
  ring

theorem tetrahedral_weighted_projector_sum (ρ : Operator 2) (hρ : IsDensityOperator ρ) :
    ∑ a : Fin 4, (((tetraRecordLaw ρ hρ).prob a : ℝ) : ℂ) • tetraProjector a
      = (1 / 2 : ℂ) • (1 : Operator 2)
        + (1 / 6 : ℂ) • ∑ j : Fin 3, ((pauliExpectation j ρ : ℝ) : ℂ) • pauliMatrix j := by
  have hcoef : ∀ a : Fin 4, ((((tetraRecordLaw ρ hρ).prob a : ℝ) : ℂ)) • tetraProjector a
      = (1 / 2 : ℂ) • ((((Matrix.trace (tetraProjector a * ρ)).re : ℂ)) • tetraProjector a) := by
    intro a
    rw [(tetrahedral_actual_record_born_law ρ hρ a).2.2, Complex.ofReal_div,
      show ((2 : ℝ) : ℂ) = (2 : ℂ) from rfl, div_eq_mul_inv, mul_comm, ← smul_smul,
      inv_eq_one_div]
  rw [Finset.sum_congr rfl fun a _ => hcoef a, ← Finset.smul_sum,
    tetrahedral_weighted_effect_sum ρ hρ]
  module

theorem tetrahedral_measurement_inverse_reconstructs :
    (∀ a : Fin 4, tetraSnapshot a = (3 : ℂ) • tetraProjector a - 1) ∧
      ∀ (ρ : Operator 2) (hρ : IsDensityOperator ρ),
        ∑ a : Fin 4, (((tetraRecordLaw ρ hρ).prob a : ℝ) : ℂ) • tetraSnapshot a = ρ := by
  refine ⟨fun _ => rfl, fun ρ hρ => ?_⟩
  have hw := tetrahedral_weighted_projector_sum ρ hρ
  have hsumw := tetrahedral_prob_sum ρ hρ
  have hstep : ∀ a : Fin 4, ((((tetraRecordLaw ρ hρ).prob a : ℝ) : ℂ)) • tetraSnapshot a
      = (3 : ℂ) • ((((tetraRecordLaw ρ hρ).prob a : ℝ) : ℂ)) • tetraProjector a
        - ((((tetraRecordLaw ρ hρ).prob a : ℝ) : ℂ)) • (1 : Operator 2) := by
    intro a
    rw [tetraSnapshot, smul_sub, smul_comm]
  calc ∑ a : Fin 4, (((tetraRecordLaw ρ hρ).prob a : ℝ) : ℂ) • tetraSnapshot a
      = (3 : ℂ) • ∑ a : Fin 4, (((tetraRecordLaw ρ hρ).prob a : ℝ) : ℂ) • tetraProjector a
          - (∑ a : Fin 4, (((tetraRecordLaw ρ hρ).prob a : ℝ) : ℂ)) • (1 : Operator 2) := by
        rw [Finset.sum_congr rfl fun a _ => hstep a, Finset.sum_sub_distrib,
          ← Finset.sum_smul, ← Finset.smul_sum]
    _ = (1 / 2 : ℂ) • (1 + ∑ j : Fin 3, ((pauliExpectation j ρ : ℝ) : ℂ) • pauliMatrix j) := by
        rw [hw, hsumw]
        module
    _ = ρ := (bloch_reconstruction ρ hρ).symm

end Qatlib.Concepts.MbqcFlow.FlowDecision
