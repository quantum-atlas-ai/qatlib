/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpatialSearch03.MainResults.LatticeDefs
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open scoped Classical BigOperators

namespace Qatlib.Papers.SpatialSearch03.MainResults

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem inner_ket_apply (w : ι) (z : QState ι) : Inner (Ket w) z = z w := by
  rw [inner_apply, Finset.sum_eq_single w]
  · simp [Ket]
  · intro b _ hb
    simp [Ket, hb]
  · intro h
    exact absurd (Finset.mem_univ w) h

theorem sum_normSq_ket (w : ι) : ∑ i, ‖Ket w i‖ ^ 2 = 1 := by
  rw [Finset.sum_eq_single w]
  · simp [Ket]
  · intro b _ hb
    rw [show Ket w b = 0 by simp [Ket, hb]]
    simp
  · intro h
    exact absurd (Finset.mem_univ w) h

theorem sum_normSq_mulVec_unitary (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (ψ : QState ι) : ∑ i, ‖((U *ᵥ ψ) i)‖ ^ 2 = ∑ j, ‖ψ j‖ ^ 2 := by
  have h := sum_normSq_mulVec_of_mem_unitaryGroup hU ψ
  simpa only [Complex.normSq_eq_norm_sq] using h

omit [DecidableEq ι] in

theorem norm_le_sqrt_sum_normSq (z : QState ι) (i : ι) :
    ‖z i‖ ≤ Real.sqrt (∑ j, ‖z j‖ ^ 2) := by
  have hsq : ‖z i‖ ^ 2 ≤ ∑ j, ‖z j‖ ^ 2 := by
    have h := Finset.single_le_sum (s := Finset.univ) (f := fun j => ‖z j‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i)
    simpa using h
  calc ‖z i‖ = Real.sqrt (‖z i‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑ j, ‖z j‖ ^ 2) := Real.sqrt_le_sqrt hsq

theorem norm_inner_ket_mulVec_le_one (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (w : ι) (ψ : QState ι) (hψ : Normalized ψ) :
    ‖Inner (Ket w) (U *ᵥ ψ)‖ ≤ 1 := by
  rw [inner_ket_apply]
  refine (norm_le_sqrt_sum_normSq (U *ᵥ ψ) w).trans ?_
  have hnorm : ∑ i, ‖((U *ᵥ ψ) i)‖ ^ 2 = 1 := by
    rw [sum_normSq_mulVec_unitary U hU ψ, hψ]
  rw [hnorm, Real.sqrt_one]

theorem norm_successAmplitude_le_one (d n : ℕ) (hn : 0 < n) (γ : ℝ)
    (w : LatticeVertex d n) (t : ℝ) : ‖successAmplitude d n γ w t‖ ≤ 1 :=
  norm_inner_ket_mulVec_le_one (HamiltonianEvolution (searchHamiltonian d n γ w) t)
    (hamiltonianEvolution_unitary (searchHamiltonian_isHermitian d n γ w) t) w
    (latticeUniform d n) (normalized_latticeUniform d n hn)

noncomputable def evolGen (H : Matrix ι ι ℂ) : Matrix ι ι ℂ := (-Complex.I) • H

theorem hamiltonianEvolution_eq_exp (H : Matrix ι ι ℂ) (t : ℝ) :
    HamiltonianEvolution H t = NormedSpace.exp (t • evolGen H) := by
  have htower : t • (-Complex.I • H) = (t : ℂ) • (-Complex.I • H) :=
    (IsScalarTower.algebraMap_smul ℂ t (x := (-Complex.I) • H)).symm
  have hc : (t : ℂ) * (-Complex.I) = -Complex.I * (t : ℂ) := by ring
  unfold HamiltonianEvolution evolGen
  rw [htower, smul_smul, hc]

theorem hasDerivAt_hamiltonianEvolution_entry (H : Matrix ι ι ℂ) (i j : ι) (t : ℝ) :
    HasDerivAt (fun u : ℝ => HamiltonianEvolution H u i j)
      ((HamiltonianEvolution H t * evolGen H) i j) t := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (𝔸 := Matrix ι ι ℂ) (evolGen H) t
  have h' : HasDerivAt (fun u : ℝ => HamiltonianEvolution H u)
      (HamiltonianEvolution H t * evolGen H) t := by
    have hfun : (fun u : ℝ => HamiltonianEvolution H u) =
        (fun u : ℝ => NormedSpace.exp (u • evolGen H)) := by
      funext u
      exact hamiltonianEvolution_eq_exp H u
    have hval : HamiltonianEvolution H t * evolGen H =
        NormedSpace.exp (t • evolGen H) * evolGen H := by
      rw [hamiltonianEvolution_eq_exp]
    rw [hfun, hval]
    exact h
  exact hasDerivAt_pi.mp (hasDerivAt_pi.mp h' i) j

theorem evolGen_mulVec_uniform (d n : ℕ) (γ : ℝ) (w : LatticeVertex d n) :
    evolGen (searchHamiltonian d n γ w) *ᵥ latticeUniform d n =
      (Complex.I * ((Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) : ℂ))⁻¹) • Ket w := by
  unfold evolGen
  rw [Matrix.smul_mulVec, searchHamiltonian_mulVec_uniform, smul_smul]
  congr 1
  ring

theorem hasDerivAt_successAmplitude (d n : ℕ) (γ : ℝ) (w : LatticeVertex d n) (t : ℝ) :
    HasDerivAt (fun u : ℝ => successAmplitude d n γ w u)
      (Complex.I * ((Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) : ℂ))⁻¹ *
        Inner (Ket w) (HamiltonianEvolution (searchHamiltonian d n γ w) t *ᵥ Ket w)) t := by
  have hterm : ∀ j : LatticeVertex d n, HasDerivAt
      (fun u : ℝ => HamiltonianEvolution (searchHamiltonian d n γ w) u w j *
        latticeUniform d n j)
      ((HamiltonianEvolution (searchHamiltonian d n γ w) t *
          evolGen (searchHamiltonian d n γ w)) w j * latticeUniform d n j) t :=
    fun j => (hasDerivAt_hamiltonianEvolution_entry (searchHamiltonian d n γ w) w j t).mul_const _
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (A := fun j : LatticeVertex d n => fun u : ℝ =>
      HamiltonianEvolution (searchHamiltonian d n γ w) u w j * latticeUniform d n j)
    (A' := fun j : LatticeVertex d n =>
      (HamiltonianEvolution (searchHamiltonian d n γ w) t *
        evolGen (searchHamiltonian d n γ w)) w j * latticeUniform d n j)
    (fun j _ => hterm j)
  have hfun : (fun u : ℝ => ∑ j ∈ Finset.univ,
        HamiltonianEvolution (searchHamiltonian d n γ w) u w j * latticeUniform d n j) =
      (fun u : ℝ => successAmplitude d n γ w u) := by
    funext u
    rw [successAmplitude, inner_ket_apply]
    rfl
  have hval : (∑ j ∈ Finset.univ,
        (HamiltonianEvolution (searchHamiltonian d n γ w) t *
          evolGen (searchHamiltonian d n γ w)) w j * latticeUniform d n j) =
      Complex.I * ((Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) : ℂ))⁻¹ *
        Inner (Ket w) (HamiltonianEvolution (searchHamiltonian d n γ w) t *ᵥ Ket w) := by
    show ((HamiltonianEvolution (searchHamiltonian d n γ w) t *
        evolGen (searchHamiltonian d n γ w)) *ᵥ latticeUniform d n) w = _
    rw [← Matrix.mulVec_mulVec, evolGen_mulVec_uniform, Matrix.mulVec_smul,
      Pi.smul_apply, smul_eq_mul]
    rw [show (HamiltonianEvolution (searchHamiltonian d n γ w) t *ᵥ Ket w) w =
        Inner (Ket w) (HamiltonianEvolution (searchHamiltonian d n γ w) t *ᵥ Ket w) from
      (inner_ket_apply w _).symm]
  rw [hfun, hval] at hsum
  exact hsum

theorem norm_deriv_successAmplitude_le (d n : ℕ) (γ : ℝ)
    (w : LatticeVertex d n) (t : ℝ) :
    ‖Complex.I * ((Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) : ℂ))⁻¹ *
        Inner (Ket w) (HamiltonianEvolution (searchHamiltonian d n γ w) t *ᵥ Ket w)‖ ≤
      (Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ))⁻¹ := by
  have hU := hamiltonianEvolution_unitary (searchHamiltonian_isHermitian d n γ w) t
  have hinner : ‖Inner (Ket w)
      (HamiltonianEvolution (searchHamiltonian d n γ w) t *ᵥ Ket w)‖ ≤ 1 :=
    norm_inner_ket_mulVec_le_one _ hU w (Ket w) (sum_normSq_ket w)
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
  rw [show ‖(((Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) : ℂ))⁻¹)‖ =
      (Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ))⁻¹ from by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]]
  exact mul_le_of_le_one_right (by positivity) hinner

theorem time_ge_amplitude (d n : ℕ) (hn : 0 < n) (γ : ℝ) (w : LatticeVertex d n)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖successAmplitude d n γ w t‖ * Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) - 1 ≤ t := by
  have hNpos : 0 < Fintype.card (LatticeVertex d n) :=
    Fintype.card_pos_iff.mpr ⟨fun _ => ⟨0, hn⟩⟩
  have hRpos : 0 < Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hNpos)
  have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) t,
      HasDerivWithinAt (fun u : ℝ => successAmplitude d n γ w u)
        (Complex.I * ((Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) : ℂ))⁻¹ *
          Inner (Ket w) (HamiltonianEvolution (searchHamiltonian d n γ w) x *ᵥ Ket w))
        (Set.Icc (0 : ℝ) t) x :=
    fun x _ => (hasDerivAt_successAmplitude d n γ w x).hasDerivWithinAt
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (a := (0 : ℝ)) (b := t)
    (f := fun u : ℝ => successAmplitude d n γ w u)
    (f' := fun x : ℝ => Complex.I *
      ((Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) : ℂ))⁻¹ *
        Inner (Ket w) (HamiltonianEvolution (searchHamiltonian d n γ w) x *ᵥ Ket w))
    (C := (Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ))⁻¹)
    hderiv (fun x _ => norm_deriv_successAmplitude_le d n γ w x)
    t ⟨ht, le_rfl⟩
  rw [sub_zero] at hmv
  have hA0 : ‖successAmplitude d n γ w 0‖ =
      (Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ))⁻¹ := by
    rw [successAmplitude_zero, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hRpos.le]
  have hsub : ‖successAmplitude d n γ w t - successAmplitude d n γ w 0‖ ≤
      t * (Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ))⁻¹ := by
    calc ‖successAmplitude d n γ w t - successAmplitude d n γ w 0‖
        ≤ (Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ))⁻¹ * t := hmv
      _ = t * (Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ))⁻¹ := by ring
  have hstep : ‖successAmplitude d n γ w t‖ ≤
      (Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ))⁻¹ +
        t * (Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ))⁻¹ := by
    have hdecomp : successAmplitude d n γ w t =
        successAmplitude d n γ w 0 +
          (successAmplitude d n γ w t - successAmplitude d n γ w 0) := by ring
    rw [hdecomp]
    calc ‖successAmplitude d n γ w 0 +
          (successAmplitude d n γ w t - successAmplitude d n γ w 0)‖
        ≤ ‖successAmplitude d n γ w 0‖ +
            ‖successAmplitude d n γ w t - successAmplitude d n γ w 0‖ := norm_add_le _ _
      _ ≤ (Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ))⁻¹ +
            t * (Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ))⁻¹ := by
          linarith [hA0, hsub]
  have hcancel : (Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ))⁻¹ *
      Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) = 1 :=
    inv_mul_cancel₀ (ne_of_gt hRpos)
  have hmul : ‖successAmplitude d n γ w t‖ *
      Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) ≤ 1 + t := by
    calc ‖successAmplitude d n γ w t‖ * Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ)
        ≤ ((Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ))⁻¹ +
            t * (Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ))⁻¹) *
          Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) :=
          mul_le_mul_of_nonneg_right hstep hRpos.le
      _ = (1 + t) * ((Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ))⁻¹ *
            Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ)) := by ring
      _ = 1 + t := by rw [hcancel, mul_one]
  linarith

theorem repetition_time_ge (d n : ℕ) (hn : 0 < n) (γ : ℝ) (w : LatticeVertex d n)
    {ε t : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : 1 / ε ≤ t) :
    (1 - ε) * Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) *
        successProbability d n γ w t ≤ t := by
  have ht0 : 0 ≤ t := le_trans (div_pos one_pos hε).le ht
  have hhalf := time_ge_amplitude d n hn γ w (t := t) ht0
  have hA1 : ‖successAmplitude d n γ w t‖ ≤ 1 := norm_successAmplitude_le_one d n hn γ w t
  have hRpos : 0 < Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) := by
    have hNpos : 0 < Fintype.card (LatticeVertex d n) :=
      Fintype.card_pos_iff.mpr ⟨fun _ => ⟨0, hn⟩⟩
    exact Real.sqrt_pos.mpr (by exact_mod_cast hNpos)
  have hbound : Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) *
      successProbability d n γ w t ≤ t + 1 := by
    unfold successProbability
    have hsq : Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) *
          ‖successAmplitude d n γ w t‖ ^ 2 =
        ‖successAmplitude d n γ w t‖ *
          (‖successAmplitude d n γ w t‖ *
            Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ)) := by ring
    rw [hsq]
    calc ‖successAmplitude d n γ w t‖ *
          (‖successAmplitude d n γ w t‖ *
            Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ))
        ≤ 1 * (t + 1) := mul_le_mul hA1 (by linarith) (by positivity) (by norm_num)
      _ = t + 1 := by ring
  have hεt : 1 ≤ t * ε := by
    rw [div_le_iff₀ hε] at ht
    linarith
  have ht1 : t + 1 ≤ (1 + ε) * t := by nlinarith
  have hprod : (1 - ε) * (1 + ε) ≤ 1 := by nlinarith [sq_nonneg ε]
  have hnonneg : (0 : ℝ) ≤ 1 - ε := by linarith
  have hfinal := mul_le_mul_of_nonneg_left hbound hnonneg
  calc (1 - ε) * Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) *
        successProbability d n γ w t
      = (1 - ε) * (Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ) *
          successProbability d n γ w t) := by ring
    _ ≤ (1 - ε) * (t + 1) := hfinal
    _ ≤ (1 - ε) * ((1 + ε) * t) := mul_le_mul_of_nonneg_left ht1 hnonneg
    _ = ((1 - ε) * (1 + ε)) * t := by ring
    _ ≤ 1 * t := mul_le_mul_of_nonneg_right hprod ht0
    _ = t := one_mul t

end Qatlib.Papers.SpatialSearch03.MainResults
