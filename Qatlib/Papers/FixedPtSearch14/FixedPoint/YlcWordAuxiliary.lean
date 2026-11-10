/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FixedPtSearch14.FixedPoint.OptimalFixedPointCore
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection

set_option autoImplicit false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint

open Qatlib
open Matrix

noncomputable def rotZ (theta : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun i => if i = 0 then Complex.exp (-(Complex.I * theta) / 2)
    else Complex.exp (Complex.I * theta / 2)

noncomputable def su2A (zeta x s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(x : ℂ), -Complex.I * s * Complex.exp (-(Complex.I * zeta));
     -Complex.I * s * Complex.exp (Complex.I * zeta), (x : ℂ)]

noncomputable def su2Prep (x s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := su2A (Real.pi / 2) x s

@[simp] theorem rotZ_zero_zero (theta : ℝ) :
    rotZ theta 0 0 = Complex.exp (-(Complex.I * theta) / 2) := by
  simp [rotZ]

@[simp] theorem rotZ_one_one (theta : ℝ) :
    rotZ theta 1 1 = Complex.exp (Complex.I * theta / 2) := by
  simp [rotZ]

@[simp] theorem rotZ_zero_one (theta : ℝ) : rotZ theta 0 1 = 0 := by
  simp [rotZ]

@[simp] theorem rotZ_one_zero (theta : ℝ) : rotZ theta 1 0 = 0 := by
  simp [rotZ]

theorem rotZ_mul (a b : ℝ) : rotZ a * rotZ b = rotZ (a + b) := by
  unfold rotZ
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  have key : (if i = 0 then Complex.exp (-(Complex.I * (a:ℂ)) / 2)
        else Complex.exp (Complex.I * (a:ℂ) / 2)) *
      (if i = 0 then Complex.exp (-(Complex.I * (b:ℂ)) / 2)
        else Complex.exp (Complex.I * (b:ℂ) / 2)) =
      if i = 0 then
        Complex.exp (-(Complex.I * (a:ℂ)) / 2) * Complex.exp (-(Complex.I * (b:ℂ)) / 2)
      else
        Complex.exp (Complex.I * (a:ℂ) / 2) * Complex.exp (Complex.I * (b:ℂ) / 2) := by
    by_cases h : i = 0 <;> simp [h]
  rw [key]
  by_cases h : i = 0
  · rw [if_pos h, if_pos h, ← Complex.exp_add, Complex.ofReal_add]
    congr 1
    ring
  · rw [if_neg h, if_neg h, ← Complex.exp_add, Complex.ofReal_add]
    congr 1
    ring

theorem rotZ_zero : rotZ 0 = 1 := by
  have h : rotZ 0 = Matrix.diagonal fun _ => (1:ℂ) := by
    unfold rotZ
    congr 1
    funext i
    by_cases h : i = 0 <;> simp [h]
  rw [h, Matrix.diagonal_one]

theorem rotZ_mul_neg (theta : ℝ) : rotZ theta * rotZ (-theta) = 1 := by
  rw [rotZ_mul, add_neg_cancel, rotZ_zero]

theorem rotZ_neg (theta : ℝ) : rotZ (-theta) = (rotZ theta)⁻¹ :=
  (Matrix.inv_eq_right_inv (rotZ_mul_neg theta)).symm

@[simp] theorem su2A_zero_zero (zeta x s : ℝ) : su2A zeta x s 0 0 = (x : ℂ) := by
  simp [su2A]

@[simp] theorem su2A_zero_one (zeta x s : ℝ) :
    su2A zeta x s 0 1 = -Complex.I * s * Complex.exp (-(Complex.I * zeta)) := by
  simp [su2A]

@[simp] theorem su2A_one_zero (zeta x s : ℝ) :
    su2A zeta x s 1 0 = -Complex.I * s * Complex.exp (Complex.I * zeta) := by
  simp [su2A]

@[simp] theorem su2A_one_one (zeta x s : ℝ) : su2A zeta x s 1 1 = (x : ℂ) := by
  simp [su2A]

theorem exp_I_pi_div_two : Complex.exp (Complex.I * (↑(Real.pi) / 2 : ℂ)) = Complex.I := by
  conv_lhs => rw [show (Complex.I * (↑(Real.pi) / 2 : ℂ)) = (↑(Real.pi) / 2 : ℂ) * Complex.I by field_simp]
  exact Complex.exp_pi_div_two_mul_I

theorem exp_neg_I_pi_div_two : Complex.exp (-(Complex.I * (↑(Real.pi) / 2 : ℂ))) = -Complex.I := by
  have h : -(Complex.I * (↑(Real.pi) / 2 : ℂ)) = -((↑(Real.pi) / 2 : ℂ) * Complex.I) := by
    field_simp
  rw [h, Complex.exp_neg, Complex.exp_pi_div_two_mul_I]
  simp

theorem su2A_pi_div_two (x s : ℝ) :
    su2A (Real.pi / 2) x s = !![(x : ℂ), -(s:ℂ); (s:ℂ), (x : ℂ)] := by
  ext i j
  rcases (show i = 0 ∨ i = 1 by revert i; decide) with hi | hi <;>
    rcases (show j = 0 ∨ j = 1 by revert j; decide) with hj | hj <;>
    subst hi <;> subst hj <;>
    simp [su2A, exp_I_pi_div_two, exp_neg_I_pi_div_two, Complex.I_mul_I, mul_comm, ← mul_assoc]

theorem su2A_neg_pi_div_two (x s : ℝ) :
    su2A (-(Real.pi / 2)) x s = !![(x : ℂ), (s:ℂ); -(s:ℂ), (x : ℂ)] := by
  ext i j
  rcases (show i = 0 ∨ i = 1 by revert i; decide) with hi | hi <;>
    rcases (show j = 0 ∨ j = 1 by revert j; decide) with hj | hj <;>
    subst hi <;> subst hj <;>
    simp [su2A, exp_I_pi_div_two, exp_neg_I_pi_div_two, Complex.I_mul_I, mul_comm, ← mul_assoc]

theorem su2A_zero (x s : ℝ) :
    su2A 0 x s = !![(x : ℂ), -Complex.I * s; -Complex.I * s, (x : ℂ)] := by
  ext i j
  rcases (show i = 0 ∨ i = 1 by revert i; decide) with hi | hi <;>
    rcases (show j = 0 ∨ j = 1 by revert j; decide) with hj | hj <;>
    subst hi <;> subst hj <;> simp [su2A]

theorem su2A_add (zeta chi x s : ℝ) :
    su2A (zeta + chi) x s = rotZ chi * su2A zeta x s * rotZ (-chi) := by
  have e00 : Complex.exp (-(Complex.I * (chi:ℂ)) / 2) *
      Complex.exp (Complex.I * (chi:ℂ) / 2) = 1 := by
    rw [← Complex.exp_add]
    have h : -(Complex.I * (chi:ℂ)) / 2 + Complex.I * (chi:ℂ) / 2 = 0 := by ring
    rw [h, Complex.exp_zero]
  have e01 : Complex.exp (-(Complex.I * (chi:ℂ)) / 2) *
      Complex.exp (-(Complex.I * (zeta:ℂ))) *
        Complex.exp (-(Complex.I * (chi:ℂ)) / 2) =
      Complex.exp (-(Complex.I * (↑(zeta:ℝ) + ↑(chi:ℝ)))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have e10 : Complex.exp (Complex.I * (chi:ℂ) / 2) *
      Complex.exp (Complex.I * (zeta:ℂ)) *
        Complex.exp (Complex.I * (chi:ℂ) / 2) =
      Complex.exp (Complex.I * (↑(zeta:ℝ) + ↑(chi:ℝ))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have e11 : Complex.exp (Complex.I * (chi:ℂ) / 2) *
      Complex.exp (-(Complex.I * (chi:ℂ)) / 2) = 1 := by
    rw [← Complex.exp_add]
    have h : Complex.I * (chi:ℂ) / 2 + (-(Complex.I * (chi:ℂ)) / 2) = 0 := by ring
    rw [h, Complex.exp_zero]
  have h00 : (rotZ chi * su2A zeta x s * rotZ (-chi)) 0 0 = su2A (zeta + chi) x s 0 0 := by
    simp [rotZ, su2A, Matrix.mul_apply, Matrix.diagonal_apply]
    have c : Complex.exp (-(Complex.I * (chi:ℂ)) / 2) * (x:ℂ) *
        Complex.exp (Complex.I * (chi:ℂ) / 2) =
        (x:ℂ) * (Complex.exp (-(Complex.I * (chi:ℂ)) / 2) *
          Complex.exp (Complex.I * (chi:ℂ) / 2)) := by ring
    rw [c, e00, mul_one]
  have h01 : (rotZ chi * su2A zeta x s * rotZ (-chi)) 0 1 = su2A (zeta + chi) x s 0 1 := by
    simp [rotZ, su2A, Matrix.mul_apply, Matrix.diagonal_apply]
    have c : Complex.exp (-(Complex.I * (chi:ℂ)) / 2) *
        (Complex.I * (s:ℂ) * Complex.exp (-(Complex.I * (zeta:ℂ)))) *
          Complex.exp (-(Complex.I * (chi:ℂ)) / 2) =
        (Complex.I * (s:ℂ)) *
          (Complex.exp (-(Complex.I * (chi:ℂ)) / 2) *
            Complex.exp (-(Complex.I * (zeta:ℂ))) *
            Complex.exp (-(Complex.I * (chi:ℂ)) / 2)) := by ring
    rw [c, e01]
  have h10 : (rotZ chi * su2A zeta x s * rotZ (-chi)) 1 0 = su2A (zeta + chi) x s 1 0 := by
    simp [rotZ, su2A, Matrix.mul_apply, Matrix.diagonal_apply]
    have c : Complex.exp (Complex.I * (chi:ℂ) / 2) *
        (Complex.I * (s:ℂ) * Complex.exp (Complex.I * (zeta:ℂ))) *
          Complex.exp (Complex.I * (chi:ℂ) / 2) =
        (Complex.I * (s:ℂ)) *
          (Complex.exp (Complex.I * (chi:ℂ) / 2) *
            Complex.exp (Complex.I * (zeta:ℂ)) *
            Complex.exp (Complex.I * (chi:ℂ) / 2)) := by ring
    rw [c, e10]
  have h11 : (rotZ chi * su2A zeta x s * rotZ (-chi)) 1 1 = su2A (zeta + chi) x s 1 1 := by
    simp [rotZ, su2A, Matrix.mul_apply, Matrix.diagonal_apply]
    have c : Complex.exp (Complex.I * (chi:ℂ) / 2) * (x:ℂ) *
        Complex.exp (-(Complex.I * (chi:ℂ)) / 2) =
        (x:ℂ) * (Complex.exp (Complex.I * (chi:ℂ) / 2) *
          Complex.exp (-(Complex.I * (chi:ℂ)) / 2)) := by ring
    rw [c, e11, mul_one]
  ext i j
  rcases (show i = 0 ∨ i = 1 by revert i; decide) with hi | hi <;>
    rcases (show j = 0 ∨ j = 1 by revert j; decide) with hj | hj <;>
    subst hi <;> subst hj <;> simp only [h00, h01, h10, h11]

theorem targetReflection_eq (beta : ℝ) :
    targetReflection beta = Complex.exp (Complex.I * (beta:ℂ) / 2) • rotZ beta := by
  have e1 : Complex.exp (Complex.I * (beta:ℂ) / 2) *
      Complex.exp (-(Complex.I * (beta:ℂ)) / 2) = 1 := by
    rw [← Complex.exp_add]
    have h : Complex.I * (beta:ℂ) / 2 + (-(Complex.I * (beta:ℂ)) / 2) = 0 := by ring
    rw [h, Complex.exp_zero]
  have e2 : Complex.exp (Complex.I * (beta:ℂ)) =
      Complex.exp (Complex.I * (beta:ℂ) / 2) * Complex.exp (Complex.I * (beta:ℂ) / 2) := by
    have h : Complex.I * (beta:ℂ) = Complex.I * (beta:ℂ) / 2 + Complex.I * (beta:ℂ) / 2 := by ring
    conv_lhs => rw [h]
    exact Complex.exp_add _ _
  ext i j
  rcases (show i = 0 ∨ i = 1 by revert i; decide) with hi | hi <;>
    rcases (show j = 0 ∨ j = 1 by revert j; decide) with hj | hj <;>
    subst hi <;> subst hj <;>
    simp [targetReflection, rotZ, Matrix.smul_apply, e1, e2]

theorem ofReal_sqrt_sq {a : ℝ} (ha : 0 ≤ a) : ((Real.sqrt a : ℝ) : ℂ) ^ 2 = (a : ℂ) := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt ha]

theorem ofReal_sqrt_mul (a b : ℝ) :
    ((Real.sqrt a : ℝ) : ℂ) * ((Real.sqrt b : ℝ) : ℂ) = ((Real.sqrt a * Real.sqrt b : ℝ) : ℂ) :=
  (Complex.ofReal_mul _ _).symm

theorem stateReflection_entry (lam alpha : ℝ) (hl : 0 ≤ lam) (hl' : lam ≤ 1) :
    stateReflection lam alpha =
      !![((1 - (lam:ℂ)) * Complex.exp (-(Complex.I * alpha)) + (lam:ℂ) : ℂ),
          (Real.sqrt (1 - lam) * Real.sqrt lam) *
            (Complex.exp (-(Complex.I * alpha)) - 1);
          (Real.sqrt lam * Real.sqrt (1 - lam)) *
            (Complex.exp (-(Complex.I * alpha)) - 1),
          ((lam:ℂ) * Complex.exp (-(Complex.I * alpha)) + (1 - (lam:ℂ)) : ℂ)] := by
  have hx : ((Real.sqrt (1 - lam) : ℝ) : ℂ) * ((Real.sqrt (1 - lam) : ℝ) : ℂ)
      = 1 - (lam : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith), Complex.ofReal_sub,
      Complex.ofReal_one]
  have hs : ((Real.sqrt lam : ℝ) : ℂ) * ((Real.sqrt lam : ℝ) : ℂ) = (lam : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hl]
  ext i j
  rcases (show i = 0 ∨ i = 1 by revert i; decide) with hi | hi <;>
    rcases (show j = 0 ∨ j = 1 by revert j; decide) with hj | hj <;>
    subst hi <;> subst hj
  · simp [stateReflection, outerProduct, ampState, Matrix.sub_apply, Matrix.smul_apply]
    rw [hx]
    ring
  · simp [stateReflection, outerProduct, ampState, Matrix.sub_apply, Matrix.smul_apply]
    ring
  · simp [stateReflection, outerProduct, ampState, Matrix.sub_apply, Matrix.smul_apply]
    ring
  · simp [stateReflection, outerProduct, ampState, Matrix.sub_apply, Matrix.smul_apply]
    rw [hs]
    ring

private theorem mul2 (P Q : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    (P * Q) i j = P i 0 * Q 0 j + P i 1 * Q 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

private theorem exp_half_sq (a : ℂ) :
    Complex.exp (a / 2) * Complex.exp (a / 2) = Complex.exp a := by
  rw [← Complex.exp_add]; congr 1; ring

private theorem exp_half_cancel (a : ℂ) :
    Complex.exp (a / 2) * Complex.exp (-a / 2) = 1 := by
  rw [← Complex.exp_add, show a / 2 + -a / 2 = 0 by ring, Complex.exp_zero]

theorem ylcWordMatrix_zero (delta lam : ℝ) : ylcWordMatrix 0 delta lam = 1 := by
  show ((List.range 0).map fun i =>
    groverIterate lam (ylcAlpha 1 (i + 1) (ylcGamma 1 delta))
      (-(ylcAlpha 1 (0 - i) (ylcGamma 1 delta)))).reverse.prod = 1
  simp

theorem ylcGamma_one {delta : ℝ} (hd : 0 < delta) (hd' : delta ≤ 1) :
    ylcGamma 1 delta = delta := by
  have h1 : 1 ≤ 1 / delta := one_le_one_div_of_le hd hd'
  rw [ylcGamma, show ((1:ℕ):ℝ) = 1 by norm_num, div_one, Real.cosh_arcosh h1, one_div_one_div]

theorem responseProb_one_eq {lam : ℝ} (hl : 0 ≤ lam) (hl' : lam ≤ 1) (delta : ℝ)
    (hd : 0 < delta) (hd' : delta < 1) : responseProb 1 delta lam = lam := by
  have hγ : ylcGamma 1 delta = delta := ylcGamma_one hd (le_of_lt hd')
  rw [responseProb_eq, hγ, cheb_one]
  have h : delta * (Real.sqrt (1 - lam) / delta) = Real.sqrt (1 - lam) := by field_simp
  rw [h]
  nlinarith [Real.mul_self_sqrt (by linarith : (0:ℝ) ≤ 1 - lam)]

theorem ylcMainIdentity_l0 (delta lam : ℝ) (hd : 0 < delta) (hd' : delta < 1)
    (hl : 0 ≤ lam) (hl' : lam ≤ 1) :
    ‖Qatlib.Foundations.PureStateMath.Inner (fun i => if i = 0 then (0:ℂ) else 1)
        (ylcWordMatrix 0 delta lam *ᵥ ampState lam)‖ ^ 2 =
      responseProb 1 delta lam := by
  rw [ylcWordMatrix_zero, Matrix.one_mulVec, responseProb_one_eq hl hl' delta hd hd']
  have h1 : (fun i : Fin 2 => if i = 0 then (0:ℂ) else 1) 1 = 1 := by simp
  have h0 : (fun i : Fin 2 => if i = 0 then (0:ℂ) else 1) 0 = 0 := by simp
  have hinner : Qatlib.Foundations.PureStateMath.Inner (fun i => if i = 0 then (0:ℂ) else 1) (ampState lam)
      = (Real.sqrt lam : ℂ) := by
    rw [Qatlib.Foundations.PureStateMath.inner_apply]
    have hsum : (∑ i : Fin 2, (starRingEnd ℂ) ((fun i : Fin 2 => if i = 0 then (0:ℂ) else 1) i)
        * ampState lam i) =
        (starRingEnd ℂ) ((fun i : Fin 2 => if i = 0 then (0:ℂ) else 1) 0) * ampState lam 0
          + (starRingEnd ℂ) ((fun i : Fin 2 => if i = 0 then (0:ℂ) else 1) 1) * ampState lam 1 :=
      Fin.sum_univ_two _
    rw [hsum, h0, h1]
    simp [ampState]
  rw [hinner, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, Real.mul_self_sqrt hl]

end Qatlib.Papers.FixedPtSearch14.FixedPoint
