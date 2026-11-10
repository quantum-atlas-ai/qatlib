/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.LcuFrame.Defs

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Foundations.MatrixGeometry.LcuFrame

variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

def invSqrt2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

def ham (β : J → ℝ) (P : J → Matrix I I ℂ) : Matrix I I ℂ :=
  ∑ j, (((β j : ℂ)) ^ 2) • P j

def phi0 (β : J → ℝ) (φ : State I) : State (J × I) := fun ji => (β ji.1 : ℂ) * φ ji.2

def applySys (σ : Matrix I I ℂ) (ψ : State (J × I)) : State (J × I) :=
  fun ji => ∑ i', σ ji.2 i' * ψ (ji.1, i')

def Vphi0 (β : J → ℝ) (P : J → Matrix I I ℂ) (φ : State I) : State (J × I) :=
  fun ji => (β ji.1 : ℂ) * (P ji.1 *ᵥ φ) ji.2

def phi1 (β : J → ℝ) (P : J → Matrix I I ℂ) (φ : State I) (E : ℝ) : State (J × I) :=
  fun ji =>
    (((Real.sqrt (1 - E ^ 2) : ℝ)) : ℂ)⁻¹ * (Vphi0 β P φ ji - (E : ℂ) * phi0 β φ ji)

def phiP (β : J → ℝ) (P : J → Matrix I I ℂ) (φ : State I) (E : ℝ) : State (J × I) :=
  fun ji => invSqrt2 * (phi0 β φ ji + Complex.I * phi1 β P φ E ji)

def phiM (β : J → ℝ) (P : J → Matrix I I ℂ) (φ : State I) (E : ℝ) : State (J × I) :=
  fun ji => invSqrt2 * (phi0 β φ ji - Complex.I * phi1 β P φ E ji)

def Gamma (β : J → ℝ) (ε : J → ℝ) : ℝ := ∑ j, (β j) ^ 2 * ε j

abbrev curry {J I : Type*} (ψ : State (J × I)) : J → State I := fun j i => ψ (j, i)

abbrev uncurry {J I : Type*} (u : J → State I) : State (J × I) := fun ji => u ji.1 ji.2

theorem uncurry_curry {J I : Type*} (ψ : State (J × I)) : uncurry (curry ψ) = ψ := by
  funext ji
  rfl

theorem inner_prod_fiber {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (u v : J → State I) :
    Inner (uncurry u) (uncurry v) = ∑ j, Inner (u j) (v j) := by
  rw [inner_apply, Fintype.sum_prod_type]
  simp only [inner_apply, uncurry]

theorem applySys_fiber {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (σ : Matrix I I ℂ) (u : J → State I) :
    applySys σ (uncurry u) = uncurry (fun j => σ *ᵥ u j) := by
  funext ji
  simp [applySys, uncurry, Matrix.mulVec, dotProduct]

theorem inner_add_left' {I : Type*} [Fintype I] [DecidableEq I] (u v w : State I) :
    Inner (u + v) w = Inner u w + Inner v w := by
  rw [inner_apply, inner_apply, inner_apply]
  simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem inner_add_right' {I : Type*} [Fintype I] [DecidableEq I] (u v w : State I) :
    Inner u (v + w) = Inner u v + Inner u w := by
  rw [inner_apply, inner_apply, inner_apply]
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem inner_sub_left' {I : Type*} [Fintype I] [DecidableEq I] (u v w : State I) :
    Inner (u - v) w = Inner u w - Inner v w := by
  rw [inner_apply, inner_apply, inner_apply]
  simp only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem inner_sub_right' {I : Type*} [Fintype I] [DecidableEq I] (u v w : State I) :
    Inner u (v - w) = Inner u v - Inner u w := by
  rw [inner_apply, inner_apply, inner_apply]
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem inner_smul_left' {I : Type*} [Fintype I] [DecidableEq I] (c : ℂ) (ψ φ : State I) :
    Inner (c • ψ) φ = (starRingEnd ℂ) c * Inner ψ φ := by
  rw [inner_apply, inner_apply]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem inner_smul_right' {I : Type*} [Fintype I] [DecidableEq I] (c : ℂ) (ψ φ : State I) :
    Inner ψ (c • φ) = c * Inner ψ φ := by
  rw [inner_apply, inner_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem inner_sum_right' {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    (ψ : State I) (s : ι → State I) :
    Inner ψ (∑ i, s i) = ∑ i, Inner ψ (s i) := by
  simp only [inner_apply, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem inner_conj_symm' {I : Type*} [Fintype I] [DecidableEq I] (ψ φ : State I) :
    (starRingEnd ℂ) (Inner ψ φ) = Inner φ ψ := by
  rw [inner_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  have h2 : (starRingEnd ℂ) ((starRingEnd ℂ) (ψ i)) = ψ i := by simp
  rw [h2]
  exact mul_comm _ _

theorem star_ofReal' (r : ℝ) : (starRingEnd ℂ) ((r : ℂ)) = ((r : ℂ)) := by
  simp

theorem applySys_add' {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (σ : Matrix I I ℂ) (ψ χ : State (J × I)) :
    applySys σ (ψ + χ) = applySys σ ψ + applySys σ χ := by
  funext ji
  simp only [applySys, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem applySys_smul' {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (σ : Matrix I I ℂ) (c : ℂ) (ψ : State (J × I)) :
    applySys σ (c • ψ) = c • applySys σ ψ := by
  funext ji
  simp only [applySys, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem applySys_sub' {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (σ : Matrix I I ℂ) (ψ χ : State (J × I)) :
    applySys σ (ψ - χ) = applySys σ ψ - applySys σ χ := by
  funext ji
  simp only [applySys, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem inner_applySys_adjoint {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (σ : Matrix I I ℂ) (hσ : σᴴ = σ) (ψ χ : State (J × I)) :
    Inner ψ (applySys σ χ) = Inner (applySys σ ψ) χ := by
  rw [← uncurry_curry ψ, ← uncurry_curry χ, applySys_fiber, applySys_fiber,
    inner_prod_fiber, inner_prod_fiber]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_mulVec_left_rect, hσ]

theorem inner_hermitian_self_real {I : Type*} [Fintype I] [DecidableEq I]
    (σ : Matrix I I ℂ) (hσ : σᴴ = σ) (φ : State I) :
    (starRingEnd ℂ) (Inner φ (σ *ᵥ φ)) = Inner φ (σ *ᵥ φ) := by
  rw [inner_apply, map_sum]
  have hmv : ∀ i : I, (σ *ᵥ φ) i = ∑ i', σ i i' * φ i' := fun i => rfl
  simp only [hmv, map_mul, map_sum, Finset.mul_sum]
  have hstar : ∀ i : I, (starRingEnd ℂ) ((starRingEnd ℂ) (φ i)) = φ i := fun i => by simp
  have hh : ∀ i i' : I, (starRingEnd ℂ) (σ i i') = σ i' i := by
    intro i i'
    have := congrFun (congrFun hσ i') i
    simpa [Matrix.conjTranspose_apply] using this
  simp only [hstar, hh]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
  ring

theorem inner_phi0_applySys_phi0 {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (β : J → ℝ) (φ ψ : State I) (σ : Matrix I I ℂ) :
    Inner (phi0 β φ) (applySys σ (phi0 β ψ))
      = (((∑ j, (β j) ^ 2 : ℝ) : ℂ)) * Inner φ (σ *ᵥ ψ) := by
  have h2 : applySys σ (phi0 β ψ) = uncurry (fun j => (β j : ℂ) • (σ *ᵥ ψ)) := by
    rw [show phi0 β ψ = uncurry (fun j => (β j : ℂ) • ψ) from rfl, applySys_fiber]
    funext ji
    simp [uncurry, Matrix.mulVec_smul]
  rw [show phi0 β φ = uncurry (fun j => (β j : ℂ) • φ) from rfl, h2, inner_prod_fiber]
  have hterm : ∀ j, Inner ((β j : ℂ) • φ) ((β j : ℂ) • (σ *ᵥ ψ))
      = (((β j) ^ 2 : ℝ) : ℂ) * Inner φ (σ *ᵥ ψ) := by
    intro j
    rw [inner_smul_left', inner_smul_right', star_ofReal']
    push_cast
    ring
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum]

theorem inner_phi0_applySys_Vphi0 {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (β : J → ℝ) (P : J → Matrix I I ℂ) (φ ψ : State I) (σ : Matrix I I ℂ) :
    Inner (phi0 β φ) (applySys σ (Vphi0 β P ψ))
      = ∑ j, (((β j) ^ 2 : ℝ) : ℂ) * Inner φ (σ *ᵥ (P j *ᵥ ψ)) := by
  have h2 : applySys σ (Vphi0 β P ψ)
      = uncurry (fun j => (β j : ℂ) • (σ *ᵥ (P j *ᵥ ψ))) := by
    rw [show Vphi0 β P ψ = uncurry (fun j => (β j : ℂ) • (P j *ᵥ ψ)) from rfl,
      applySys_fiber]
    funext ji
    simp [uncurry, Matrix.mulVec_smul]
  rw [show phi0 β φ = uncurry (fun j => (β j : ℂ) • φ) from rfl, h2, inner_prod_fiber]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left', inner_smul_right', star_ofReal']
  push_cast
  ring

theorem inner_Vphi0_applySys_phi0 {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (β : J → ℝ) (P : J → Matrix I I ℂ) (φ ψ : State I) (σ : Matrix I I ℂ) :
    Inner (Vphi0 β P φ) (applySys σ (phi0 β ψ))
      = ∑ j, (((β j) ^ 2 : ℝ) : ℂ) * Inner (P j *ᵥ φ) (σ *ᵥ ψ) := by
  have h2 : applySys σ (phi0 β ψ) = uncurry (fun j => (β j : ℂ) • (σ *ᵥ ψ)) := by
    rw [show phi0 β ψ = uncurry (fun j => (β j : ℂ) • ψ) from rfl, applySys_fiber]
    funext ji
    simp [uncurry, Matrix.mulVec_smul]
  rw [show Vphi0 β P φ = uncurry (fun j => (β j : ℂ) • (P j *ᵥ φ)) from rfl,
    h2, inner_prod_fiber]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left', inner_smul_right', star_ofReal']
  push_cast
  ring

theorem inner_Vphi0_applySys_Vphi0 {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (β : J → ℝ) (P : J → Matrix I I ℂ) (φ ψ : State I) (σ : Matrix I I ℂ) :
    Inner (Vphi0 β P φ) (applySys σ (Vphi0 β P ψ))
      = ∑ j, (((β j) ^ 2 : ℝ) : ℂ)
          * Inner (P j *ᵥ φ) (σ *ᵥ (P j *ᵥ ψ)) := by
  have h2 : applySys σ (Vphi0 β P ψ)
      = uncurry (fun j => (β j : ℂ) • (σ *ᵥ (P j *ᵥ ψ))) := by
    rw [show Vphi0 β P ψ = uncurry (fun j => (β j : ℂ) • (P j *ᵥ ψ)) from rfl,
      applySys_fiber]
    funext ji
    simp [uncurry, Matrix.mulVec_smul]
  rw [show Vphi0 β P φ = uncurry (fun j => (β j : ℂ) • (P j *ᵥ φ)) from rfl,
    h2, inner_prod_fiber]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left', inner_smul_right', star_ofReal']
  push_cast
  ring

omit [DecidableEq J] [DecidableEq I] in

theorem phi0_normalized (β : J → ℝ) (φ : State I)
    (hβ : ∑ j, (β j) ^ 2 = 1) (hφ : Normalized φ) : Normalized (phi0 β φ) := by
  unfold Normalized phi0
  rw [Fintype.sum_prod_type]
  have hterm : ∀ j : J, ∑ i : I, ‖(β j : ℂ) * φ i‖ ^ 2 = (β j) ^ 2 * ∑ i, ‖φ i‖ ^ 2 := by
    intro j
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hterm]
  rw [← Finset.sum_mul, hβ, hφ, one_mul]

theorem expectation_eq8 (β : J → ℝ) (P : J → Matrix I I ℂ) (σ : Matrix I I ℂ)
    (ε : J → ℝ) (φ : State I) (E : ℝ)
    (hβ : ∑ j, (β j) ^ 2 = 1)
    (_hφ : Normalized φ)
    (hσherm : σᴴ = σ) (_hσsq : σ * σ = 1)
    (hPherm : ∀ j, (P j)ᴴ = P j) (_hPsq : ∀ j, P j * P j = 1)
    (hcomm : ∀ j, P j * σ * P j = (ε j : ℂ) • σ)
    (_hε : ∀ j, ε j = 1 ∨ ε j = -1)
    (hEig : ham β P *ᵥ φ = (E : ℂ) • φ)
    (hE : E ^ 2 < 1) :
    Inner (phiP β P φ E) (applySys σ (phiP β P φ E))
        = (((1 / 2 : ℝ) * (1 + (Gamma β ε - E ^ 2) / (1 - E ^ 2)) : ℝ) : ℂ)
            * Inner φ (σ *ᵥ φ) ∧
      Inner (phiM β P φ E) (applySys σ (phiM β P φ E))
        = (((1 / 2 : ℝ) * (1 + (Gamma β ε - E ^ 2) / (1 - E ^ 2)) : ℝ) : ℂ)
            * Inner φ (σ *ᵥ φ) := by
  have hEpos : (0 : ℝ) < 1 - E ^ 2 := by nlinarith [hE]
  have hspos : 0 < Real.sqrt (1 - E ^ 2) := Real.sqrt_pos.2 hEpos
  set g : ℂ := Inner φ (σ *ᵥ φ) with hg
  have hg_real : (starRingEnd ℂ) g = g := by
    rw [hg]
    exact inner_hermitian_self_real σ hσherm φ

  have hB00 : Inner (phi0 β φ) (applySys σ (phi0 β φ)) = g := by
    rw [inner_phi0_applySys_phi0 β φ φ σ, hβ]
    simp [hg]
  have hham : ham β P *ᵥ φ = ∑ j, (((β j) ^ 2 : ℝ) : ℂ) • (P j *ᵥ φ) := by
    rw [ham, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_mulVec]
    congr 1
    push_cast
    ring
  have hB01_sum : Inner φ (σ *ᵥ (ham β P *ᵥ φ))
      = ∑ j, (((β j) ^ 2 : ℝ) : ℂ) * Inner φ (σ *ᵥ (P j *ᵥ φ)) := by
    rw [hham, Matrix.mulVec_sum, inner_sum_right']
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, inner_smul_right']
  have hB01 : Inner (phi0 β φ) (applySys σ (Vphi0 β P φ)) = (E : ℂ) * g := by
    rw [inner_phi0_applySys_Vphi0]
    rw [← hB01_sum, hEig, Matrix.mulVec_smul, inner_smul_right']
  have hblock (j : J) : Inner (P j *ᵥ φ) (σ *ᵥ (P j *ᵥ φ)) = ((ε j : ℝ) : ℂ) * g := by
    rw [inner_mulVec_left_rect, hPherm j]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [hcomm j, Matrix.smul_mulVec, inner_smul_right']
  have hB11 : Inner (Vphi0 β P φ) (applySys σ (Vphi0 β P φ))
      = ((Gamma β ε : ℝ) : ℂ) * g := by
    rw [inner_Vphi0_applySys_Vphi0]
    simp_rw [hblock]
    have hterm : ∀ j, (((β j) ^ 2 : ℝ) : ℂ) * (((ε j : ℝ) : ℂ) * g)
        = ((((β j) ^ 2 * ε j : ℝ)) : ℂ) * g := by
      intro j
      push_cast
      ring
    simp_rw [hterm]
    rw [← Finset.sum_mul, ← Complex.ofReal_sum]
    rfl
  have hB10 : Inner (Vphi0 β P φ) (applySys σ (phi0 β φ)) = (E : ℂ) * g := by
    rw [← inner_conj_symm' (ψ := applySys σ (phi0 β φ)) (φ := Vphi0 β P φ),
      ← inner_applySys_adjoint σ hσherm (ψ := phi0 β φ) (χ := Vphi0 β P φ),
      hB01, map_mul, star_ofReal', hg_real]

  set cs : ℂ := (((Real.sqrt (1 - E ^ 2) : ℝ)) : ℂ)⁻¹ with hcs_def
  set d : State (J × I) := Vphi0 β P φ - (E : ℂ) • phi0 β φ with hd
  have hphi1 : phi1 β P φ E = cs • d := rfl
  have hAd : applySys σ d
      = applySys σ (Vphi0 β P φ) - (E : ℂ) • applySys σ (phi0 β φ) := by
    rw [hd, applySys_sub', applySys_smul']
  have hInner11 : Inner (phi1 β P φ E) (applySys σ (phi1 β P φ E))
      = (starRingEnd ℂ) cs * cs *
          (Inner (Vphi0 β P φ) (applySys σ (Vphi0 β P φ))
           - (E : ℂ) * Inner (Vphi0 β P φ) (applySys σ (phi0 β φ))
           - (E : ℂ) * Inner (phi0 β φ) (applySys σ (Vphi0 β P φ))
           + (E : ℂ) * (E : ℂ)
              * Inner (phi0 β φ) (applySys σ (phi0 β φ))) := by
    rw [hphi1, applySys_smul', inner_smul_left', inner_smul_right', hAd]
    rw [inner_sub_left', inner_sub_right', inner_sub_right',
      inner_smul_left', inner_smul_left', inner_smul_right', inner_smul_right']
    rw [star_ofReal']
    ring
  have hcs_conj : (starRingEnd ℂ) cs = cs := by
    rw [hcs_def, map_inv₀]
    exact congrArg Inv.inv (star_ofReal' _)
  have hcs_prod : (starRingEnd ℂ) cs * cs = (((1 - E ^ 2 : ℝ)) : ℂ)⁻¹ := by
    rw [hcs_conj, hcs_def, ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (le_of_lt hEpos), Complex.ofReal_inv]
  have hne : (1 : ℂ) - (E : ℂ) ^ 2 ≠ 0 := by
    have hc : (1 : ℂ) - (E : ℂ) ^ 2 = ((1 - E ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hc]
    exact_mod_cast (ne_of_gt hEpos)
  have hInner11_val : Inner (phi1 β P φ E) (applySys σ (phi1 β P φ E))
      = (((Gamma β ε - E ^ 2) / (1 - E ^ 2) : ℝ) : ℂ) * g := by
    rw [hInner11, hB11, hB10, hB01, hB00, hcs_prod]
    push_cast
    field_simp [hne]
    ring

  have hcross1 : Inner (phi0 β φ) (applySys σ (phi1 β P φ E)) = 0 := by
    rw [hphi1, applySys_smul', inner_smul_right', hAd]
    rw [inner_sub_right', inner_smul_right', hB01, hB00]
    ring
  have hcross2 : Inner (phi1 β P φ E) (applySys σ (phi0 β φ)) = 0 := by
    rw [hphi1, inner_smul_left', hd]
    rw [inner_sub_left', inner_smul_left', hB10, hB00]
    rw [star_ofReal']
    ring

  have hphiP : phiP β P φ E = invSqrt2 • (phi0 β φ + Complex.I • phi1 β P φ E) := rfl
  have hAphiP : applySys σ (phiP β P φ E)
      = invSqrt2 • (applySys σ (phi0 β φ)
        + Complex.I • applySys σ (phi1 β P φ E)) := by
    rw [hphiP, applySys_smul', applySys_add', applySys_smul']
  have hinnerP : Inner (phiP β P φ E) (applySys σ (phiP β P φ E))
      = (starRingEnd ℂ) invSqrt2 * invSqrt2 *
          Inner (phi0 β φ + Complex.I • phi1 β P φ E)
            (applySys σ (phi0 β φ) + Complex.I • applySys σ (phi1 β P φ E)) := by
    rw [hAphiP, hphiP, inner_smul_left', inner_smul_right']
    ring
  have hexpandP : Inner (phi0 β φ + Complex.I • phi1 β P φ E)
      (applySys σ (phi0 β φ) + Complex.I • applySys σ (phi1 β P φ E))
      = Inner (phi0 β φ) (applySys σ (phi0 β φ))
        + Complex.I * Inner (phi0 β φ) (applySys σ (phi1 β P φ E))
        + (starRingEnd ℂ) Complex.I * Inner (phi1 β P φ E) (applySys σ (phi0 β φ))
        + (starRingEnd ℂ) Complex.I * Complex.I
            * Inner (phi1 β P φ E) (applySys σ (phi1 β P φ E)) := by
    rw [inner_add_left', inner_add_right', inner_add_right',
      inner_smul_right', inner_smul_left', inner_smul_left', inner_smul_right']
    ring
  have hconjI : (starRingEnd ℂ) Complex.I * Complex.I = 1 := by
    rw [Complex.conj_I, neg_mul, Complex.I_mul_I]
    ring
  have hinvSqrt2 : (starRingEnd ℂ) invSqrt2 * invSqrt2 = (1 / 2 : ℂ) := by
    unfold invSqrt2
    rw [show (starRingEnd ℂ) (((Real.sqrt 2 : ℝ)) : ℂ)⁻¹
        = (((Real.sqrt 2 : ℝ)) : ℂ)⁻¹ by
      rw [map_inv₀]
      exact congrArg Inv.inv (star_ofReal' _)]
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hcoef : (1 / 2 : ℂ) * (g + (((Gamma β ε - E ^ 2) / (1 - E ^ 2) : ℝ) : ℂ) * g)
      = (((1 / 2 : ℝ) * (1 + (Gamma β ε - E ^ 2) / (1 - E ^ 2)) : ℝ) : ℂ) * g := by
    push_cast
    field_simp [hne]
  have hfinalP : Inner (phiP β P φ E) (applySys σ (phiP β P φ E))
      = (((1 / 2 : ℝ) * (1 + (Gamma β ε - E ^ 2) / (1 - E ^ 2)) : ℝ) : ℂ) * g := by
    rw [hinnerP, hexpandP, hB00, hcross1, hcross2, hInner11_val, hconjI, hinvSqrt2]
    simp only [mul_zero, add_zero, one_mul]
    exact hcoef
  have hphiM : phiM β P φ E = invSqrt2 • (phi0 β φ - Complex.I • phi1 β P φ E) := rfl
  have hAphiM : applySys σ (phiM β P φ E)
      = invSqrt2 • (applySys σ (phi0 β φ)
        - Complex.I • applySys σ (phi1 β P φ E)) := by
    rw [hphiM, applySys_smul', applySys_sub', applySys_smul']
  have hinnerM : Inner (phiM β P φ E) (applySys σ (phiM β P φ E))
      = (starRingEnd ℂ) invSqrt2 * invSqrt2 *
          Inner (phi0 β φ - Complex.I • phi1 β P φ E)
            (applySys σ (phi0 β φ) - Complex.I • applySys σ (phi1 β P φ E)) := by
    rw [hAphiM, hphiM, inner_smul_left', inner_smul_right']
    ring
  have hexpandM : Inner (phi0 β φ - Complex.I • phi1 β P φ E)
      (applySys σ (phi0 β φ) - Complex.I • applySys σ (phi1 β P φ E))
      = Inner (phi0 β φ) (applySys σ (phi0 β φ))
        - Complex.I * Inner (phi0 β φ) (applySys σ (phi1 β P φ E))
        - (starRingEnd ℂ) Complex.I * Inner (phi1 β P φ E) (applySys σ (phi0 β φ))
        + (starRingEnd ℂ) Complex.I * Complex.I
            * Inner (phi1 β P φ E) (applySys σ (phi1 β P φ E)) := by
    rw [inner_sub_left', inner_sub_right', inner_sub_right',
      inner_smul_right', inner_smul_left', inner_smul_left', inner_smul_right']
    ring
  have hfinalM : Inner (phiM β P φ E) (applySys σ (phiM β P φ E))
      = (((1 / 2 : ℝ) * (1 + (Gamma β ε - E ^ 2) / (1 - E ^ 2)) : ℝ) : ℂ) * g := by
    rw [hinnerM, hexpandM, hB00, hcross1, hcross2, hInner11_val, hconjI, hinvSqrt2]
    simp only [mul_zero, sub_zero, one_mul]
    exact hcoef
  exact ⟨hfinalP, hfinalM⟩

end Qatlib.Foundations.MatrixGeometry.LcuFrame
