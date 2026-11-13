/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.OperatorErrors.OperatorError
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Coercive bounds for Hermitian Sylvester expressions

For matrices `S` and `T` bounded below by a positive scalar `c` times the identity, this module
proves the operator norm bound `(2 * c) * ‖X‖ ≤ ‖S * X + X * T‖` for Hermitian `X`. It uses
normalized quadratic forms and matrix positivity, in the framework of [Bhatia1997].

Applying this estimate to `X = S - T` yields `hermitian_square_difference_bound`, which controls
the distance between two Hermitian matrices by the distance between their squares under the same
positive lower bound.

## Main statements

* `hermitian_sylvester_opNorm_coercive`: the operator norm coercivity estimate.
* `hermitian_square_difference_bound`: the resulting bound for differences of squares.

## References

* [Bhatia, 1997][Bhatia1997]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The absolute value of the quadratic form of `D` on a normalized state is bounded by the
operator norm of `D`. -/
private theorem sylvester_quadratic_bound (D : Matrix N N ℂ) (v : QState N) (hv : Normalized v) :
    ‖Qatlib.Foundations.PureStateMath.Inner v (D *ᵥ v)‖ ≤ ‖D‖ := by
  have hn := (normalized_iff_norm_toEuclidean_fromVec v).mp hv
  have hm := Matrix.l2_opNorm_mulVec D (toEuclidean_fromVec v)
  change ‖toEuclidean_fromVec (D *ᵥ v)‖ ≤ ‖D‖*‖toEuclidean_fromVec v‖ at hm
  rw [hn, mul_one] at hm
  rw [← inner_euclidean_fromVec]
  exact (norm_inner_le_norm _ _).trans (by simpa only [hn, one_mul] using hm)

/-- If `A - c • 1` is positive semidefinite, the real part of the quadratic form of `A` on any
normalized state is at least `c`. -/
private theorem sylvester_quadratic_lower (A : Matrix N N ℂ) (c : ℝ)
    (hA : (A-c•(1:Matrix N N ℂ)).PosSemidef) (v : QState N) (hv : Normalized v) :
    c ≤ (Qatlib.Foundations.PureStateMath.Inner v (A *ᵥ v)).re := by
  have hi : Qatlib.Foundations.PureStateMath.Inner v v = 1 :=
      (normalized_iff_inner_self v).mp hv
  have he : Qatlib.Foundations.PureStateMath.Inner v ((A-c•(1:Matrix N N ℂ)) *ᵥ v) = Qatlib.Foundations.PureStateMath.Inner v (A *ᵥ v)-(c:ℂ) := by
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Qatlib.Foundations.PureStateMath.Inner, dotProduct_sub, dotProduct_smul, RCLike.real_smul_eq_coe_mul,
      show star v ⬝ᵥ v = 1 from hi, mul_one]
    rfl
  have h := hA.re_dotProduct_nonneg v
  change 0 ≤ (Qatlib.Foundations.PureStateMath.Inner v ((A-c•(1:Matrix N N ℂ)) *ᵥ v)).re at h
  rw [he, Complex.sub_re, Complex.ofReal_re] at h
  linarith

/-- If `S` and `T` are bounded below by `c • 1` with `c > 0`, then `(2 * c) * ‖X‖ ≤ ‖S * X + X *
T‖` for every Hermitian `X`. -/
theorem hermitian_sylvester_opNorm_coercive (S T X : Matrix N N ℂ) (c : ℝ)
    (hc : 0 < c) (hX : X.IsHermitian)
    (hS : (S-c•(1:Matrix N N ℂ)).PosSemidef)
    (hT : (T-c•(1:Matrix N N ℂ)).PosSemidef) :
    (2*c)*‖X‖ ≤ ‖S*X+X*T‖ := by
  let ev : N → ℂ := fun i => (hX.eigenvalues i : ℂ)
  have heig (i : N) : (2*c)*|hX.eigenvalues i| ≤ ‖S*X+X*T‖ := by
    let v : QState N := ⇑(hX.eigenvectorBasis i)
    let l := hX.eigenvalues i
    have hv : Normalized v := (normalized_iff_norm_toEuclidean_fromVec v).mpr
      (hX.eigenvectorBasis.norm_eq_one i)
    have hx : X *ᵥ v = (l:ℂ) • v := by
      simpa only [RCLike.real_smul_eq_coe_smul] using! hX.mulVec_eigenvectorBasis i
    have hstar : star v ᵥ* X = (l:ℂ) • star v := by
      have h := congrArg star hx
      simpa only [Matrix.star_mulVec, hX.eq, star_smul, Complex.star_def,
          Complex.conj_ofReal] using h
    have htterm : Qatlib.Foundations.PureStateMath.Inner v (X *ᵥ (T *ᵥ v)) = (l:ℂ)*Qatlib.Foundations.PureStateMath.Inner v (T *ᵥ v) := by
      rw [Qatlib.Foundations.PureStateMath.Inner, Matrix.dotProduct_mulVec, hstar,
          smul_dotProduct]
      rfl
    have hsterm : Qatlib.Foundations.PureStateMath.Inner v (S *ᵥ (X *ᵥ v)) = (l:ℂ)*Qatlib.Foundations.PureStateMath.Inner v (S *ᵥ v) := by
      rw [hx, Matrix.mulVec_smul, Qatlib.Foundations.PureStateMath.Inner, dotProduct_smul]
      rfl
    have hquad : Qatlib.Foundations.PureStateMath.Inner v ((S*X+X*T) *ᵥ v) =
        (l:ℂ)*(Qatlib.Foundations.PureStateMath.Inner v (S *ᵥ v)+Qatlib.Foundations.PureStateMath.Inner v (T *ᵥ v)) := by
      change star v ⬝ᵥ ((S*X+X*T) *ᵥ v) = _
      rw [Matrix.add_mulVec, dotProduct_add]
      change Qatlib.Foundations.PureStateMath.Inner v
          ((S*X) *ᵥ v)+Qatlib.Foundations.PureStateMath.Inner v ((X*T) *ᵥ v) = _
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hsterm, htterm]
      ring
    have hs := sylvester_quadratic_lower S c hS v hv
    have ht := sylvester_quadratic_lower T c hT v hv
    have hlow : 2*c ≤ (Qatlib.Foundations.PureStateMath.Inner v (S *ᵥ v)+Qatlib.Foundations.PureStateMath.Inner v (T *ᵥ v)).re := by
      rw [Complex.add_re]; linarith
    calc
      (2*c)*|l| ≤ |l| *(Qatlib.Foundations.PureStateMath.Inner v (S *ᵥ v)+Qatlib.Foundations.PureStateMath.Inner v (T *ᵥ v)).re := by
        nlinarith [mul_le_mul_of_nonneg_left hlow (abs_nonneg l)]
      _ ≤ |l| *‖Qatlib.Foundations.PureStateMath.Inner v (S *ᵥ v)+Qatlib.Foundations.PureStateMath.Inner v (T *ᵥ v)‖ :=
        mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (abs_nonneg l)
      _ = ‖Qatlib.Foundations.PureStateMath.Inner v ((S*X+X*T) *ᵥ v)‖ := by
        rw [hquad, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ _ := sylvester_quadratic_bound _ v hv
  have hn : ‖X‖ = ‖ev‖ := by
    conv_lhs => rw [hX.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    change ‖(hX.eigenvectorUnitary : Matrix N N ℂ)*Matrix.diagonal ev*
      (star hX.eigenvectorUnitary : unitary (Matrix N N ℂ))‖ = ‖ev‖
    rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  have hb : ‖X‖ ≤ ‖S*X+X*T‖/(2*c) := by
    rw [hn]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs]
    apply (le_div_iff₀ (by positivity : 0 < 2*c)).mpr
    simpa only [ev, mul_comm] using heig i
  have h := (le_div_iff₀ (by positivity : 0 < 2*c)).mp hb
  nlinarith

/-- For Hermitian `S` and `T` bounded below by `c • 1` with `c > 0`, their operator norm
distance is at most `‖S * S - T * T‖ / (2 * c)`. -/
theorem hermitian_square_difference_bound (S T : Matrix N N ℂ) (c : ℝ)
    (hc : 0 < c) (hS : S.IsHermitian) (hT : T.IsHermitian)
    (hs : (S-c•(1:Matrix N N ℂ)).PosSemidef)
    (ht : (T-c•(1:Matrix N N ℂ)).PosSemidef) :
    ‖S-T‖ ≤ ‖S*S-T*T‖/(2*c) := by
  have h := hermitian_sylvester_opNorm_coercive S T (S-T) c hc (hS.sub hT) hs ht
  have he : S*(S-T)+(S-T)*T=S*S-T*T := by
    rw [Matrix.mul_sub, Matrix.sub_mul]; abel
  rw [he] at h
  apply (le_div_iff₀ (by positivity : 0 < 2*c)).mpr
  nlinarith

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
