/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Defs
import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Euler
import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Kraus
import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Tools
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic

set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open scoped BigOperators Classical

open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.ClusterPatterns.CnotPatterns
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire
open scoped BigOperators Classical
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra

theorem mpRoundedAngle_3_pi_div_four : mpRoundedAngle 3 (Real.pi / 4) = Real.pi / 4 := by
  unfold mpRoundedAngle
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hinner : ((Real.pi / 4) * (2 ^ (3 : ℕ)) / (2 * Real.pi) + 1 / 2 : ℝ) = 3 / 2 := by
    rw [show (2 ^ (3 : ℕ) : ℝ) = 8 by norm_num]
    field_simp [hpi]
    ring
  rw [hinner]
  have hfloor : Int.floor (3 / 2 : ℝ) = (1 : ℤ) :=
    Int.floor_eq_on_Ico 1 (3 / 2) ⟨by norm_num, by norm_num⟩
  rw [hfloor, Int.cast_one, mul_one]
  rw [show (2 ^ (3 : ℕ) : ℝ) = 8 by norm_num]
  field_simp [hpi]
  ring

theorem mpRoundedAngle_3_zero : mpRoundedAngle 3 0 = 0 := by
  unfold mpRoundedAngle
  have hinner : (0 * (2 ^ (3 : ℕ)) / (2 * Real.pi) + 1 / 2 : ℝ) = 1 / 2 := by
    rw [zero_mul, zero_div, zero_add]
  rw [hinner]
  have hfloor : Int.floor (1 / 2 : ℝ) = (0 : ℤ) :=
    Int.floor_eq_on_Ico 0 (1 / 2) ⟨by norm_num, by norm_num⟩
  rw [hfloor, Int.cast_zero, mul_zero, zero_div]

theorem euler_round3 :
    (fun j : Fin 5 => mpRoundedAngle 3 (Qatlib.Concepts.ClusterPatterns.CnotPatterns.theta (Real.pi / 4) j))
      = Qatlib.Concepts.ClusterPatterns.CnotPatterns.theta (Real.pi / 4) := by
  funext j
  by_cases hj : j = 0
  · subst hj
    simp [Qatlib.Concepts.ClusterPatterns.CnotPatterns.theta]
    exact mpRoundedAngle_3_pi_div_four
  · have hz : Qatlib.Concepts.ClusterPatterns.CnotPatterns.theta (Real.pi / 4) j = 0 := by simp [Qatlib.Concepts.ClusterPatterns.CnotPatterns.theta, hj]
    rw [hz, mpRoundedAngle_3_zero]

theorem clause7_counter_clause8 :
    ¬ (∀ (θ : Fin 5 → ℝ) (b : ℕ), 1 ≤ b →
        ∃ V : Matrix (Fin 2) (Fin 2) ℂ,
          V * V.conjTranspose = 1 ∧ V.conjTranspose * V = 1 ∧
          (∀ (s : Fin 5 → Bool) (ρ : Operator 2),
            ∑ z : Fin 5 → Bool,
                (mpPatternKraus (mpEulerPattern fun j => mpRoundedAngle b (θ j))
                    (Uniform (Reg 5)) s z) * ρ
                  * (mpPatternKraus (mpEulerPattern fun j => mpRoundedAngle b (θ j))
                      (Uniform (Reg 5)) s z).conjTranspose
              = (1 / 32 : ℂ) • (V * ρ * V.conjTranspose))
          ∧ ∀ (s z : Fin 5 → Bool) (i j : Fin 2),
              ‖(mpPatternKraus (mpEulerPattern fun j => mpRoundedAngle b (θ j))
                  (Uniform (Reg 5)) s z) i j
                - (mpPatternKraus (mpEulerPattern θ) (Uniform (Reg 5)) s z) i j‖
                ≤ 2 ^ 11 * (2 : ℝ) ^ (-(b : ℤ))) := by
  intro h
  obtain ⟨V, hV1, _hV2, hVc, _hbnd⟩ :=
      h (Qatlib.Concepts.ClusterPatterns.CnotPatterns.theta (Real.pi / 4)) 3 (by norm_num)
  rw [euler_round3] at hVc
  have hz := hVc Qatlib.Concepts.ClusterPatterns.CnotPatterns.s0 (1 : Operator 2)
  have hent := congrArg (fun M : Operator 2 => M 0 0) hz
  beta_reduce at hent
  rw [Qatlib.Concepts.ClusterPatterns.CnotPatterns.euler_channel_I00] at hent
  have hR : ((1 / 32 : ℂ) • (V * (1 : Operator 2) * V.conjTranspose)) 0 0
      = ((1 / 32 : ℂ)) := by
    rw [Matrix.mul_one, hV1]
    simp [Matrix.smul_apply, Matrix.one_apply]
  rw [hR] at hent
  have h32 : ((1 / 32 : ℂ)) = (((1 / 32 : ℝ) : ℂ)) := by norm_num
  rw [h32] at hent
  rw [Complex.ofReal_inj] at hent
  have he2 : (1 + Real.exp (-(Real.pi / 4)) ^ 2 : ℝ) ^ 2 = 4 := by
    have hh := hent
    field_simp at hh
    nlinarith
  have hpos : (0 : ℝ) < 1 + Real.exp (-(Real.pi / 4)) ^ 2 := by positivity
  have h12 : (1 + Real.exp (-(Real.pi / 4)) ^ 2 : ℝ) = 2 := by
    have hfac : ((1 + Real.exp (-(Real.pi / 4)) ^ 2) - 2)
        * ((1 + Real.exp (-(Real.pi / 4)) ^ 2) + 2)
        = (1 + Real.exp (-(Real.pi / 4)) ^ 2) ^ 2 - 4 := by ring
    have hm : ((1 + Real.exp (-(Real.pi / 4)) ^ 2) - 2)
        * ((1 + Real.exp (-(Real.pi / 4)) ^ 2) + 2) = 0 := by
      rw [hfac]
      nlinarith
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hm with hh | hh
    · nlinarith
    · nlinarith
  have he1 : Real.exp (-(Real.pi / 4)) ^ 2 = 1 := by nlinarith
  have he : Real.exp (-(Real.pi / 4)) = 1 := by
    rcases sq_eq_one_iff.mp he1 with hh | hh
    · exact hh
    · have hexp : 0 < Real.exp (-(Real.pi / 4)) := Real.exp_pos _
      nlinarith
  have hpi : -(Real.pi / 4) = 0 := by rw [← Real.exp_eq_one_iff]; exact he
  have hzpi : Real.pi = 0 := by nlinarith
  exact Real.pi_ne_zero hzpi
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire
open scoped BigOperators Classical
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
open Qatlib.Concepts.ClusterPatterns.CnotPatterns
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra

def IsRealC (c : ℂ) : Prop := star c = c

theorem isRealC_ofReal (r : ℝ) : IsRealC ((r : ℝ) : ℂ) := Complex.conj_ofReal _

theorem isRealC_zero : IsRealC (0 : ℂ) := by simp [IsRealC]

theorem isRealC_one : IsRealC (1 : ℂ) := by simp [IsRealC]

theorem isRealC_neg {a : ℂ} (ha : IsRealC a) : IsRealC (-a) := by
  simp only [IsRealC] at ha ⊢
  rw [star_neg, ha]

theorem isRealC_add {a b : ℂ} (ha : IsRealC a) (hb : IsRealC b) : IsRealC (a + b) := by
  simp only [IsRealC] at ha ⊢
  rw [star_add, ha, hb]

theorem isRealC_mul {a b : ℂ} (ha : IsRealC a) (hb : IsRealC b) : IsRealC (a * b) := by
  simp only [IsRealC] at ha ⊢
  rw [star_mul', ha, hb]

theorem isRealC_star {a : ℂ} (ha : IsRealC a) : IsRealC (star a) := by
  simp only [IsRealC] at ha ⊢
  rw [star_star, ha]

theorem isRealC_inv {a : ℂ} (ha : IsRealC a) : IsRealC a⁻¹ := by
  simp only [IsRealC] at ha ⊢
  rw [star_inv₀, ha]

theorem isRealC_sum {ι : Type*} {s : Finset ι} {f : ι → ℂ}
    (h : ∀ i ∈ s, IsRealC (f i)) : IsRealC (∑ i ∈ s, f i) := by
  simp only [IsRealC] at h ⊢
  rw [star_sum]
  exact Finset.sum_congr rfl (fun i hi => h i hi)

theorem isRealC_prod {ι : Type*} {s : Finset ι} {f : ι → ℂ}
    (h : ∀ i ∈ s, IsRealC (f i)) : IsRealC (∏ i ∈ s, f i) := by
  simp only [IsRealC] at h ⊢
  rw [star_prod]
  exact Finset.prod_congr rfl (fun i hi => h i hi)

theorem isRealC_sv (α : ℝ) (o b : Bool) : IsRealC (mpSVector α o b) := by
  rw [sv_eq_ofReal]
  exact isRealC_ofReal _

theorem isRealC_star_sv (α : ℝ) (o b : Bool) : IsRealC (star (mpSVector α o b)) := by
  rw [star_sv]
  exact isRealC_sv α o b

theorem isRealC_bitPhase (b : Bool) : IsRealC (Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase b) := by
  rcases b with rfl | rfl
  · show IsRealC (1 : ℂ)
    exact isRealC_one
  · show IsRealC (-1 : ℂ)
    exact isRealC_neg isRealC_one

theorem eulerPhase_real (x : Reg 6) : IsRealC (eulerPhase x) := by
  unfold eulerPhase
  repeat' apply isRealC_mul
  all_goals exact isRealC_bitPhase _

theorem euler_ent_shape (θ θ' : Fin 5 → ℝ) :
    (mpEulerPattern θ).entangler = (mpEulerPattern θ').entangler := rfl

theorem euler_load_shape (θ θ' : Fin 5 → ℝ) :
    mpLoadMatrix (mpEulerPattern θ) (Uniform (Reg 5))
      = mpLoadMatrix (mpEulerPattern θ') (Uniform (Reg 5)) := rfl

theorem euler_EL_gen (θ : Fin 5 → ℝ) (d : Reg 6) (y : Reg 1) :
    ((mpEulerPattern θ).entangler
        * mpLoadMatrix (mpEulerPattern θ) (Uniform (Reg 5))) d y
      = if d 0 = y 0 then (eulerPhase d * ((Real.sqrt 32 : ℝ) : ℂ)⁻¹) else 0 := by
  rw [euler_ent_shape θ (theta 0), euler_load_shape θ (theta 0)]
  exact euler_EL 0 d y

theorem core_eq_gen {n w m : ℕ} (P : MpPattern n w m)
    (resource : QState (Reg (w + m - n))) (s : Fin w → Bool)
    (xp : Fin (2 ^ m)) (yp : Fin (2 ^ n)) :
    core P resource s xp yp = corePre P resource s xp ((bitVecEquiv n).symm yp) := by
  simp only [core, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm,
    Equiv.refl_apply]

theorem euler_corePre_real (θ : Fin 5 → ℝ) (s : Fin 5 → Bool) (xp : Fin 2) (y : Reg 1) :
    IsRealC (corePre (mpEulerPattern θ) (Uniform (Reg 5)) s xp y) := by
  unfold corePre
  simp only [Matrix.of_apply]
  apply isRealC_mul
  · apply isRealC_prod
    intro k _
    by_cases h : (mpEulerPattern θ).zCorr k s && mpOutBit (mpEulerPattern θ) s xp k
    · rw [if_pos h]
      show IsRealC (-1 : ℂ)
      exact isRealC_neg isRealC_one
    · rw [if_neg h]
      exact isRealC_one
  · apply isRealC_sum
    intro c _
    apply isRealC_mul
    · apply isRealC_mul
      · apply isRealC_prod
        intro j _
        exact isRealC_star_sv _ _ _
      · by_cases h : ∀ v : Fin 1,
            c (Fin.natAdd 5 v) = mpOutBit (mpEulerPattern θ) s xp v
        · rw [if_pos h]
          exact isRealC_one
        · rw [if_neg h]
          exact isRealC_zero
    · rw [euler_EL_gen θ c y]
      by_cases h : c 0 = y 0
      · rw [if_pos h]
        apply isRealC_mul
        · exact eulerPhase_real c
        · show IsRealC (((Real.sqrt 32 : ℝ) : ℂ)⁻¹)
          exact isRealC_inv (isRealC_ofReal _)
      · rw [if_neg h]
        exact isRealC_zero

theorem euler_core_real (θ : Fin 5 → ℝ) (s : Fin 5 → Bool) (xp yp : Fin 2) :
    IsRealC (core (mpEulerPattern θ) (Uniform (Reg 5)) s xp yp) := by
  rw [core_eq_gen]
  exact euler_corePre_real θ s xp _

theorem euler_v_real (θ : Fin 5 → ℝ) (s z : Fin 5 → Bool) :
    IsRealC (∏ j : Fin 5, mpSVector (mpAdaptiveAngle (mpEulerPattern θ) s j) (s j) (z j)) := by
  apply isRealC_prod
  intro j _
  exact isRealC_sv _ _ _

theorem euler_kraus_real (θ : Fin 5 → ℝ) (s z : Fin 5 → Bool) (i j : Fin 2) :
    IsRealC (mpPatternKraus (mpEulerPattern θ) (Uniform (Reg 5)) s z i j) := by
  rw [kraus_eq_smul_core, Matrix.smul_apply, smul_eq_mul]
  apply isRealC_mul
  · exact euler_v_real θ s z
  · exact euler_core_real θ s i j

def e01 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun i j => if i = 0 ∧ j = 1 then (1 : ℂ) else 0

theorem e01_apply (i j : Fin 2) : e01 i j = if i = 0 ∧ j = 1 then (1 : ℂ) else 0 := rfl

theorem e01_0j (j : Fin 2) : e01 0 j = if j = 1 then (1 : ℂ) else 0 := by
  rw [e01_apply]
  by_cases hj : j = 1
  · subst hj
    simp
  · simp [hj]

theorem e01_1j (j : Fin 2) : e01 1 j = 0 := by
  rw [e01_apply]
  simp

theorem mul_e01_conj (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (A * e01 * A.conjTranspose) 0 1 = A 0 0 * star (A 1 1) := by
  have hleft : ∀ i j : Fin 2, (A * e01) i j = if j = 1 then A i 0 else 0 := by
    intro i j
    rw [Matrix.mul_apply, Fin.sum_univ_two, e01_0j, e01_1j]
    by_cases hj : j = 1
    · subst hj
      simp
    · simp [hj]
  rw [Matrix.mul_apply, Fin.sum_univ_two, hleft, hleft,
    Matrix.conjTranspose_apply, Matrix.conjTranspose_apply]
  simp

theorem euler_channel_e01_01 (θ : Fin 5 → ℝ) :
    ((∑ z : Fin 5 → Bool,
        (mpPatternKraus (mpEulerPattern θ) (Uniform (Reg 5)) s0 z) * e01
          * (mpPatternKraus (mpEulerPattern θ) (Uniform (Reg 5)) s0 z).conjTranspose) 0 1)
      = ∑ z : Fin 5 → Bool,
          (mpPatternKraus (mpEulerPattern θ) (Uniform (Reg 5)) s0 z 0 0)
            * star (mpPatternKraus (mpEulerPattern θ) (Uniform (Reg 5)) s0 z 1 1) := by
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro z _
  exact mul_e01_conj _

theorem euler_channel_e01_real (θ : Fin 5 → ℝ) :
    IsRealC ((∑ z : Fin 5 → Bool,
        (mpPatternKraus (mpEulerPattern θ) (Uniform (Reg 5)) s0 z) * e01
          * (mpPatternKraus (mpEulerPattern θ) (Uniform (Reg 5)) s0 z).conjTranspose) 0 1) := by
  rw [euler_channel_e01_01]
  apply isRealC_sum
  intro z _
  apply isRealC_mul
  · exact euler_kraus_real θ s0 z 0 0
  · exact isRealC_star (euler_kraus_real θ s0 z 1 1)

theorem mpFin1Gate_t_apply (i j : Fin 2) :
    mpFin1Gate (FiniteGateCode.t 0) i j
      = tGate ((bitVecEquiv 1).symm i 0) ((bitVecEquiv 1).symm j 0) := by
  have h1 : finiteCodeMatrix 1 (FiniteGateCode.t 0) = wireGate 1 ⟨0, by omega⟩ tGate := rfl
  simp only [mpFin1Gate, Matrix.reindex_apply, Matrix.submatrix_apply, h1, wireGate_apply]
  rw [if_pos (by intro k hk; fin_cases k; exact absurd rfl hk)]
  simp only [Fin.fin_one_eq_zero]

theorem mpFin1Gate_t_00 : mpFin1Gate (FiniteGateCode.t 0) 0 0 = 1 := by
  rw [mpFin1Gate_t_apply]
  rw [show ((bitVecEquiv 1).symm 0 : Reg 1) 0 = false from (bitVec1_symm).2.1]
  simp [tGate, Rz]

theorem mpFin1Gate_t_11 : mpFin1Gate (FiniteGateCode.t 0) 1 1
    = Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) := by
  rw [mpFin1Gate_t_apply]
  rw [show ((bitVecEquiv 1).symm 1 : Reg 1) 0 = true from (bitVec1_symm).2.2]
  simp [tGate, Rz]

theorem conj_smul_e01 (c : ℂ) (T : Matrix (Fin 2) (Fin 2) ℂ) :
    ((c • T) * e01 * (c • T).conjTranspose) 0 1
      = (c * star c) * (T 0 0 * star (T 1 1)) := by
  rw [Matrix.conjTranspose_smul, smul_mul_assoc, smul_mul_smul, Matrix.smul_apply, smul_eq_mul,
    mul_e01_conj]

theorem exp_mul_I_star (φ : ℝ) :
    Complex.exp ((φ : ℂ) * Complex.I) * star (Complex.exp ((φ : ℂ) * Complex.I)) = 1 := by
  rw [mul_comm]
  rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_ofReal_mul_I]
  norm_num

theorem star_ofReal' (r : ℝ) : star (((r : ℝ) : ℂ)) = ((r : ℝ) : ℂ) := Complex.conj_ofReal _

theorem star_exp_pi4_ne :
    star (Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I))
      ≠ Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) := by
  intro h
  rw [Complex.star_def, Complex.conj_eq_iff_im,
    Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_four] at h
  norm_num at h

theorem clause7_counter_clause7 :
    ¬ (∀ g : FiniteGateCode,
        (g = FiniteGateCode.h 0 ∨ g = FiniteGateCode.x 0
          ∨ g = FiniteGateCode.t 0 ∨ g = FiniteGateCode.tdg 0) →
        ∃ θ : Fin 5 → ℝ,
          ∃ V : Matrix (Fin 2) (Fin 2) ℂ,
            V * V.conjTranspose = 1 ∧ V.conjTranspose * V = 1 ∧
            ∃ φ : ℝ, V = Complex.exp (Complex.ofReal φ * Complex.I) • mpFin1Gate g ∧
            ∀ (s : Fin 5 → Bool) (ρ : Operator 2),
              ∑ z : Fin 5 → Bool,
                  (mpPatternKraus (mpEulerPattern θ) (Uniform (Reg 5)) s z) * ρ
                    * (mpPatternKraus (mpEulerPattern θ) (Uniform (Reg 5)) s z).conjTranspose
                = (1 / 32 : ℂ) • (V * ρ * V.conjTranspose)) := by
  intro h
  have hg : (FiniteGateCode.t 0 = FiniteGateCode.h 0
        ∨ FiniteGateCode.t 0 = FiniteGateCode.x 0
        ∨ FiniteGateCode.t 0 = FiniteGateCode.t 0
        ∨ FiniteGateCode.t 0 = FiniteGateCode.tdg 0) :=
    Or.inr (Or.inr (Or.inl rfl))
  obtain ⟨θ, V, _hV1, _hV2, φ, hVφ, hV⟩ := h (FiniteGateCode.t 0) hg
  have hz := hV s0 e01
  have hent := congrArg (fun M : Operator 2 => M 0 1) hz
  beta_reduce at hent
  have hR : ((1 / 32 : ℂ) • (V * e01 * V.conjTranspose)) 0 1
      = ((1 / 32 : ℂ) * (Complex.exp ((φ : ℂ) * Complex.I)
            * star (Complex.exp ((φ : ℂ) * Complex.I)))
          * (mpFin1Gate (FiniteGateCode.t 0) 0 0
            * star (mpFin1Gate (FiniteGateCode.t 0) 1 1))) := by
    rw [Matrix.smul_apply, smul_eq_mul, hVφ, conj_smul_e01]
    ring
  rw [hR] at hent
  have hreal := euler_channel_e01_real θ
  simp only [IsRealC] at hreal
  rw [hent] at hreal
  have hT : (mpFin1Gate (FiniteGateCode.t 0) 0 0)
        * star (mpFin1Gate (FiniteGateCode.t 0) 1 1)
      = star (Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)) := by
    rw [mpFin1Gate_t_00, mpFin1Gate_t_11, one_mul]
  rw [exp_mul_I_star, mul_one, hT] at hreal
  have hst32 : star ((1 / 32 : ℂ)) = ((1 / 32 : ℂ)) := by
    rw [show ((1 / 32 : ℂ)) = (((1 / 32 : ℝ) : ℂ)) by norm_num]
    exact Complex.conj_ofReal _
  rw [star_mul', hst32, star_star] at hreal
  have h32ne : ((1 / 32 : ℂ)) ≠ 0 := by norm_num
  have heq := mul_left_cancel₀ h32ne hreal
  exact star_exp_pi4_ne heq.symm
end Qatlib.Concepts.ClusterPatterns.CnotPatterns
