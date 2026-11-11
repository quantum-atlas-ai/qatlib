/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RiemCircuit26.ShiftRules.GradientCoefficient

/-!
# Hessian parameter-shift coefficients

Defines the two-parameter trace cost from successive conjugations and computes its pure and
mixed second derivatives at the origin. Hermitian involutions yield exact shift formulas: a
three-evaluation central difference for the pure derivative and a four-corner difference for the
mixed derivative. See [LaiEtAl2026].

## Main statements

* `hessian_second_xx_parameterShift`: gives the pure second-derivative shift formula.
* `hessian_second_xy_parameterShift`: gives the mixed second-derivative shift formula.

## References

* [Lai et al., 2026][LaiEtAl2026]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open Matrix
open scoped Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.RiemCircuit26.ShiftRules
open Qatlib.Papers.RiemCircuit26.HessianGeometry

/-- The trace cost after conjugating `ψ` first by the `P` evolution at `x` and then by the `Q`
evolution at `y`. -/
noncomputable def hessianCost {p : ℕ} (O ψ P Q : Mat p) (x y : ℝ) : ℂ :=
  (O * conjEvol (halfI Q) (conjEvol (halfI P) ψ x) y).trace

/-- For Hermitian `P`, differentiating the two-parameter cost in `x` replaces the initial matrix
by `comm (halfI P) ψ` inside the two conjugations. -/
theorem hasDerivAt_hessianCost_x {p : ℕ} (O ψ P Q : Mat p) (hP : Pᴴ = P) (x y : ℝ) :
    HasDerivAt (fun x' : ℝ => hessianCost O ψ P Q x' y)
      ((O * conjEvol (halfI Q) (conjEvol (halfI P) (HessianGeometry.comm (halfI P) ψ) x) y).trace) x := by
  have hΩ : (halfI P)ᴴ = -halfI P := halfI_star P hP
  have hA : HasDerivAt
      (fun x' : ℝ => (evol (halfI Q) y * conjEvol (halfI P) ψ x') * (evol (halfI Q) y)ᴴ)
      ((evol (halfI Q) y * conjEvol (halfI P) (HessianGeometry.comm (halfI P) ψ) x) *
        (evol (halfI Q) y)ᴴ) x :=
    ((hasDerivAt_conjEvol (halfI P) ψ hΩ x).const_mul (evol (halfI Q) y)).mul_const
      ((evol (halfI Q) y)ᴴ)
  have h := hasDerivAt_trace (hA.const_mul O)
  have hfun : (fun x' : ℝ => hessianCost O ψ P Q x' y) =
      fun x' : ℝ =>
        (O * ((evol (halfI Q) y * conjEvol (halfI P) ψ x') * (evol (halfI Q) y)ᴴ)).trace := by
    funext x'
    simp only [hessianCost, conjEvol]
  have hval : (O * ((evol (halfI Q) y * conjEvol (halfI P) (HessianGeometry.comm (halfI P) ψ) x) *
        (evol (halfI Q) y)ᴴ)).trace =
      (O * conjEvol (halfI Q) (conjEvol (halfI P) (HessianGeometry.comm (halfI P) ψ) x) y).trace := by
    simp only [conjEvol]
  rw [hfun, ← hval]
  exact h

/-- For Hermitian `P`, the `x` derivative at zero is the trace cost of the `Q` conjugation of
`comm (halfI P) ψ`. -/
theorem hasDerivAt_hessianCost_x_zero {p : ℕ} (O ψ P Q : Mat p) (hP : Pᴴ = P) (y : ℝ) :
    HasDerivAt (fun x : ℝ => hessianCost O ψ P Q x y)
      ((O * conjEvol (halfI Q) (HessianGeometry.comm (halfI P) ψ) y).trace) 0 := by
  simpa using hasDerivAt_hessianCost_x O ψ P Q hP 0 y

/-- Transfers a nested commutator through the trace: `trace (O * comm A (comm B ψ)) = -trace (ψ
* comm (comm A O) B)`. -/
theorem trace_O_comm_comm_general {p : ℕ} (O ψ A B : Mat p) :
    (O * HessianGeometry.comm A (HessianGeometry.comm B ψ)).trace = -((ψ * HessianGeometry.comm (HessianGeometry.comm A O) B).trace) := by
  have h1 : (O * HessianGeometry.comm A (HessianGeometry.comm B ψ)).trace = (HessianGeometry.comm B ψ * HessianGeometry.comm O A).trace :=
    trace_mul_commutator O A (HessianGeometry.comm B ψ)
  have h2 : (ψ * HessianGeometry.comm (HessianGeometry.comm A O) B).trace = (HessianGeometry.comm (HessianGeometry.comm A O) B * ψ).trace := by
    rw [trace_mul_commutator ψ (HessianGeometry.comm A O) B, Matrix.trace_mul_comm,
      trace_commutator_cycle ψ (HessianGeometry.comm A O) B]
  have h3 : (HessianGeometry.comm B ψ * HessianGeometry.comm O A).trace = -((HessianGeometry.comm A O * HessianGeometry.comm B ψ).trace) := by
    rw [comm_neg_swap O A, Matrix.mul_neg, Matrix.trace_neg, Matrix.trace_mul_comm]
  have h4 : (HessianGeometry.comm (HessianGeometry.comm A O) B * ψ).trace = (HessianGeometry.comm A O * HessianGeometry.comm B ψ).trace := by
    rw [trace_commutator_cycle (HessianGeometry.comm A O) B ψ, Matrix.trace_mul_comm]
  rw [h1, h2, h3, h4]

/-- Expresses the repeated `halfI P` commutator trace as one quarter of `(ψ * comm (comm P O)
P).trace`. -/
theorem trace_halfI_xx {p : ℕ} (O ψ P : Mat p) :
    (O * HessianGeometry.comm (halfI P) (HessianGeometry.comm (halfI P) ψ)).trace =
      (1 / 4 : ℂ) * (ψ * HessianGeometry.comm (HessianGeometry.comm P O) P).trace := by
  rw [comm_halfI_left]
  rw [comm_halfI_left, comm_smul_right]
  rw [smul_smul]
  rw [Matrix.mul_smul, Matrix.trace_smul]
  rw [trace_O_comm_comm_general O ψ P P]
  have hcc : (Complex.I / 2) * (Complex.I / 2) = -(1 / 4 : ℂ) := by
    rw [show (Complex.I / 2) * (Complex.I / 2) = Complex.I ^ 2 * (1 / 4 : ℂ) by ring,
      Complex.I_sq]
    ring
  rw [hcc]
  ring

/-- Expresses the mixed `halfI Q`, `halfI P` commutator trace as one quarter of `(ψ * comm (comm
Q O) P).trace`. -/
theorem trace_halfI_xy {p : ℕ} (O ψ P Q : Mat p) :
    (O * HessianGeometry.comm (halfI Q) (HessianGeometry.comm (halfI P) ψ)).trace =
      (1 / 4 : ℂ) * (ψ * HessianGeometry.comm (HessianGeometry.comm Q O) P).trace := by
  rw [comm_halfI_left]
  rw [comm_halfI_left, comm_smul_right]
  rw [smul_smul]
  rw [Matrix.mul_smul, Matrix.trace_smul]
  rw [trace_O_comm_comm_general O ψ Q P]
  have hcc : (Complex.I / 2) * (Complex.I / 2) = -(1 / 4 : ℂ) := by
    rw [show (Complex.I / 2) * (Complex.I / 2) = Complex.I ^ 2 * (1 / 4 : ℂ) by ring,
      Complex.I_sq]
    ring
  rw [hcc]
  ring

/-- For Hermitian `P`, the pure `x` second derivative at the origin is one quarter of `(ψ * comm
(comm P O) P).trace` [LaiEtAl2026]. -/
theorem hessian_second_xx {p : ℕ} (O ψ P Q : Mat p) (hP : Pᴴ = P) :
    deriv (fun x : ℝ => deriv (fun x' : ℝ => hessianCost O ψ P Q x' 0) x) 0 =
      (1 / 4 : ℂ) * (ψ * HessianGeometry.comm (HessianGeometry.comm P O) P).trace := by
  have hfun : (fun x : ℝ => deriv (fun x' : ℝ => hessianCost O ψ P Q x' 0) x) =
      fun x : ℝ => (O * conjEvol (halfI P) (HessianGeometry.comm (halfI P) ψ) x).trace := by
    funext x
    simpa using (hasDerivAt_hessianCost_x O ψ P Q hP x 0).deriv
  rw [hfun]
  have hd := hasDerivAt_trace_conjEvol_second (halfI P) O ψ (halfI_star P hP)
  rw [hd.deriv]
  exact trace_halfI_xx O ψ P

/-- For Hermitian `P` and `Q`, the derivative at `y = 0` of the `x` derivative at zero is the
trace of the nested half-generator commutator. -/
theorem hasDerivAt_hessianCost_xy_zero {p : ℕ} (O ψ P Q : Mat p) (hP : Pᴴ = P)
    (hQ : Qᴴ = Q) :
    HasDerivAt (fun y : ℝ => deriv (fun x : ℝ => hessianCost O ψ P Q x y) 0)
      ((O * HessianGeometry.comm (halfI Q) (HessianGeometry.comm (halfI P) ψ)).trace) 0 := by
  have hfun : (fun y : ℝ => deriv (fun x : ℝ => hessianCost O ψ P Q x y) 0) =
      fun y : ℝ => (O * conjEvol (halfI Q) (HessianGeometry.comm (halfI P) ψ) y).trace := by
    funext y
    exact (hasDerivAt_hessianCost_x_zero O ψ P Q hP y).deriv
  rw [hfun]
  exact hasDerivAt_trace_conjEvol_zero (halfI Q) O (HessianGeometry.comm (halfI P) ψ)
      (halfI_star Q hQ)

/-- For Hermitian `P` and `Q`, the mixed derivative at the origin, differentiating in `x` then
`y`, is one quarter of `(ψ * comm (comm Q O) P).trace` [LaiEtAl2026]. -/
theorem hessian_second_xy {p : ℕ} (O ψ P Q : Mat p) (hP : Pᴴ = P) (hQ : Qᴴ = Q) :
    deriv (fun y : ℝ => deriv (fun x : ℝ => hessianCost O ψ P Q x y) 0) 0 =
      (1 / 4 : ℂ) * (ψ * HessianGeometry.comm (HessianGeometry.comm Q O) P).trace := by
  have h := hasDerivAt_hessianCost_xy_zero O ψ P Q hP hQ
  rw [h.deriv]
  exact trace_halfI_xy O ψ P Q

/-- At `y = 0`, the two-parameter cost reduces to `gradientCost O ψ P x`. -/
theorem hessianCost_y_zero {p : ℕ} (O ψ P Q : Mat p) (x : ℝ) :
    hessianCost O ψ P Q x 0 = gradientCost O ψ P x := by
  simp [hessianCost, gradientCost]

/-- For a Hermitian involution `P`, the sum of the conjugated matrices at shifts ±π/2 is `ψ + P
* ψ * P`. -/
theorem conjEvol_add_pi_div_two {p : ℕ} (P ψ : Mat p) (hP : Pᴴ = P) (hP2 : P * P = 1) :
    conjEvol (halfI P) ψ (Real.pi / 2) + conjEvol (halfI P) ψ (-(Real.pi / 2)) =
      ψ + P * ψ * P := by
  rw [conjEvol_pi_div_two P ψ hP hP2, conjEvol_neg_pi_div_two P ψ hP hP2, ← smul_add]
  let X : Mat p := Complex.I • P
  have hX : X * ψ * X = -(P * ψ * P) := by
    change (Complex.I • P) * ψ * (Complex.I • P) = -(P * ψ * P)
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I]
    simp
  have hexp : (1 + X) * ψ * (1 - X) + (1 - X) * ψ * (1 + X) =
      (2 : ℝ) • (ψ + P * ψ * P) := by
    change (1 + X) * ψ * (1 - X) + (1 - X) * ψ * (1 + X) =
      (2 : ℝ) • (ψ + P * ψ * P)
    rw [show (1 + X) * ψ * (1 - X) = ψ - ψ * X + X * ψ - X * ψ * X by noncomm_ring,
      show (1 - X) * ψ * (1 + X) = ψ + ψ * X - X * ψ - X * ψ * X by noncomm_ring, hX]
    module
  rw [hexp, smul_smul]
  simp

/-- For a Hermitian involution `P`, the sum of the two `x`-shifted costs minus twice the origin
cost equals `(O * (P * ψ * P - ψ)).trace`. -/
theorem hessianCost_xx_centralDiff {p : ℕ} (O ψ P Q : Mat p) (hP : Pᴴ = P)
    (hP2 : P * P = 1) :
    hessianCost O ψ P Q (Real.pi / 2) 0 + hessianCost O ψ P Q (-(Real.pi / 2)) 0 -
        2 * hessianCost O ψ P Q 0 0 =
      (O * (P * ψ * P - ψ)).trace := by
  rw [hessianCost_y_zero O ψ P Q (Real.pi / 2), hessianCost_y_zero O ψ P Q (-(Real.pi / 2)),
    hessianCost_y_zero O ψ P Q 0]
  simp only [gradientCost, conjEvol_zero]
  have h2 : (2 : ℂ) * (O * ψ).trace = (O * ((2 : ℂ) • ψ)).trace := by
    rw [← smul_eq_mul, ← Matrix.trace_smul, ← Matrix.mul_smul]
  rw [h2, ← Matrix.trace_add, ← Matrix.mul_add, ← Matrix.trace_sub, ← Matrix.mul_sub]
  congr 1
  rw [conjEvol_add_pi_div_two P ψ hP hP2, two_smul]
  abel

/-- For an involution `P`, one quarter of the repeated commutator trace equals one half of `(O *
(P * ψ * P - ψ)).trace`. -/
theorem trace_comm_comm_eq {p : ℕ} (O ψ P : Mat p) (hP2 : P * P = 1) :
    (1 / 4 : ℂ) * (ψ * HessianGeometry.comm (HessianGeometry.comm P O) P).trace =
      (1 / 2 : ℂ) * (O * (P * ψ * P - ψ)).trace := by
  have hcomm : HessianGeometry.comm (HessianGeometry.comm P O) P = (2 : ℂ) • (P * O * P - O) := by
    unfold HessianGeometry.comm
    rw [show (P * O - O * P) * P = P * O * P - O by
      rw [Matrix.sub_mul, Matrix.mul_assoc O P P, hP2, Matrix.mul_one]]
    rw [show P * (P * O - O * P) = O - P * O * P by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc P P O, hP2, Matrix.one_mul,
        ← Matrix.mul_assoc P O P]]
    module
  have htr : (ψ * (P * O * P - O)).trace = (O * (P * ψ * P - ψ)).trace := by
    have h1 : (ψ * (P * O * P)).trace = (O * (P * ψ * P)).trace := by
      rw [show ψ * (P * O * P) = (ψ * P) * (O * P) by noncomm_ring,
        Matrix.trace_mul_comm (ψ * P) (O * P),
        show (O * P) * (ψ * P) = O * (P * ψ * P) by noncomm_ring]
    have h2 : (ψ * O).trace = (O * ψ).trace := Matrix.trace_mul_comm ψ O
    rw [Matrix.mul_sub, Matrix.trace_sub, h1, h2, Matrix.mul_sub, Matrix.trace_sub]
  rw [hcomm, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, htr]
  ring

/-- For a Hermitian involution `P`, the pure `x` second derivative at the origin is one half of
the central cost difference at shifts ±π/2 [LaiEtAl2026]. -/
theorem hessian_second_xx_parameterShift {p : ℕ} (O ψ P Q : Mat p) (hP : Pᴴ = P) (hP2 : P * P = 1) :
    deriv (fun x : ℝ => deriv (fun x' : ℝ => hessianCost O ψ P Q x' 0) x) 0 =
      (1 / 2 : ℂ) * (hessianCost O ψ P Q (Real.pi / 2) 0 +
        hessianCost O ψ P Q (-(Real.pi / 2)) 0 - 2 * hessianCost O ψ P Q 0 0) := by
  rw [hessian_second_xx O ψ P Q hP, hessianCost_xx_centralDiff O ψ P Q hP hP2]
  exact trace_comm_comm_eq O ψ P hP2

/-- For a Hermitian involution `Q`, the difference of the `y`-shifted costs at fixed `x` equals
the trace of `O` times `Complex.I • comm Q (conjEvol (halfI P) ψ x)`. -/
theorem hessianCost_y_diff {p : ℕ} (O ψ P Q : Mat p) (hQ : Qᴴ = Q) (hQ2 : Q * Q = 1)
    (x : ℝ) :
    hessianCost O ψ P Q x (Real.pi / 2) - hessianCost O ψ P Q x (-(Real.pi / 2)) =
      (O * (Complex.I • HessianGeometry.comm Q (conjEvol (halfI P) ψ x))).trace := by
  simp only [hessianCost]
  rw [← Matrix.trace_sub, ← Matrix.mul_sub,
    conjEvol_sub_eq Q (conjEvol (halfI P) ψ x) hQ hQ2]

/-- For Hermitian involutions `P` and `Q`, the signed four-corner cost difference at shifts ±π/2
equals `(ψ * comm (comm Q O) P).trace`. -/
theorem fourCorner_eq {p : ℕ} (O ψ P Q : Mat p) (hP : Pᴴ = P) (hQ : Qᴴ = Q)
    (hP2 : P * P = 1) (hQ2 : Q * Q = 1) :
    hessianCost O ψ P Q (Real.pi / 2) (Real.pi / 2) -
        hessianCost O ψ P Q (Real.pi / 2) (-(Real.pi / 2)) -
        hessianCost O ψ P Q (-(Real.pi / 2)) (Real.pi / 2) +
        hessianCost O ψ P Q (-(Real.pi / 2)) (-(Real.pi / 2)) =
      (ψ * HessianGeometry.comm (HessianGeometry.comm Q O) P).trace := by
  have hfour :
      hessianCost O ψ P Q (Real.pi / 2) (Real.pi / 2) -
          hessianCost O ψ P Q (Real.pi / 2) (-(Real.pi / 2)) -
          hessianCost O ψ P Q (-(Real.pi / 2)) (Real.pi / 2) +
          hessianCost O ψ P Q (-(Real.pi / 2)) (-(Real.pi / 2)) =
      (hessianCost O ψ P Q (Real.pi / 2) (Real.pi / 2) -
          hessianCost O ψ P Q (Real.pi / 2) (-(Real.pi / 2))) -
        (hessianCost O ψ P Q (-(Real.pi / 2)) (Real.pi / 2) -
          hessianCost O ψ P Q (-(Real.pi / 2)) (-(Real.pi / 2))) := by
    ring
  rw [hfour, hessianCost_y_diff O ψ P Q hQ hQ2 (Real.pi / 2),
    hessianCost_y_diff O ψ P Q hQ hQ2 (-(Real.pi / 2))]
  have hdiff : Complex.I • HessianGeometry.comm Q (conjEvol (halfI P) ψ (Real.pi / 2)) -
      Complex.I • HessianGeometry.comm Q (conjEvol (halfI P) ψ (-(Real.pi / 2))) =
      -HessianGeometry.comm Q (HessianGeometry.comm P ψ) := by
    rw [← smul_sub]
    have hc : HessianGeometry.comm Q (conjEvol (halfI P) ψ (Real.pi / 2)) -
        HessianGeometry.comm Q (conjEvol (halfI P) ψ (-(Real.pi / 2))) =
        HessianGeometry.comm Q (conjEvol (halfI P) ψ (Real.pi / 2) -
          conjEvol (halfI P) ψ (-(Real.pi / 2))) := by
      simp only [HessianGeometry.comm, Matrix.mul_sub, Matrix.sub_mul]
      noncomm_ring
    rw [hc, conjEvol_sub_eq P ψ hP hP2, comm_smul_right, smul_smul, Complex.I_mul_I]
    simp
  rw [← Matrix.trace_sub, ← Matrix.mul_sub, hdiff, Matrix.mul_neg, Matrix.trace_neg,
    trace_O_comm_comm_general O ψ Q P]
  ring

/-- For Hermitian involutions `P` and `Q`, the mixed derivative at the origin is one quarter of
the signed four-corner cost difference at shifts ±π/2 [LaiEtAl2026]. -/
theorem hessian_second_xy_parameterShift {p : ℕ} (O ψ P Q : Mat p) (hP : Pᴴ = P) (hQ : Qᴴ = Q) (hP2 : P * P = 1) (hQ2 : Q * Q = 1) :
    deriv (fun y : ℝ => deriv (fun x : ℝ => hessianCost O ψ P Q x y) 0) 0 =
      (1 / 4 : ℂ) * (hessianCost O ψ P Q (Real.pi / 2) (Real.pi / 2) -
        hessianCost O ψ P Q (Real.pi / 2) (-(Real.pi / 2)) -
        hessianCost O ψ P Q (-(Real.pi / 2)) (Real.pi / 2) +
        hessianCost O ψ P Q (-(Real.pi / 2)) (-(Real.pi / 2))) := by
  rw [hessian_second_xy O ψ P Q hP hQ, fourCorner_eq O ψ P Q hP hQ hP2 hQ2]

end Qatlib.Papers.RiemCircuit26.ShiftRules
