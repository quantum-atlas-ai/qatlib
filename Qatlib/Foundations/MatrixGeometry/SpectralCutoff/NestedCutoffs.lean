/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.SpectralCutoff.Commutators

/-!
# Commutators with nested spectral cutoffs

For `Δ ≤ Λ`, expands a commutator compressed at `Δ` using factors compressed at `Λ` and terms
passing through energies above `Λ`. The theorem `nested_cutoff_commutator_norm` bounds the
resulting three contributions, using contraction of spectral sandwiches. See
[HejaziZiniArrazola2024] for related background.

## Main statements

* `nested_cutoff_commutator`: For `Δ ≤ Λ`, the commutator compressed at `Δ` splits into the `Δ`
  compression of the commutator of the `Λ`-compressed factors and two signed terms passing
  through `high H hH Λ`.
* `nested_cutoff_commutator_norm`: For ordered cutoffs, the norm of the lower-cutoff commutator
  is bounded by twice the product of the higher-cutoff factor norms and the two cross-subspace
  norm products.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- For `Δ ≤ Λ`, the commutator compressed at `Δ` splits into the `Δ` compression of the
commutator of the `Λ`-compressed factors and two signed terms passing through `high H hH Λ`. -/
theorem nested_cutoff_commutator (H : Matrix I I ℂ) (hH : H.IsHermitian)
    (Δ Λ : ℝ) (hΔ : Δ ≤ Λ) (A B : Matrix I I ℂ) :
    low H hH Δ*(A*B-B*A)*low H hH Δ =
      low H hH Δ*((low H hH Λ*A*low H hH Λ)*(low H hH Λ*B*low H hH Λ)-
        (low H hH Λ*B*low H hH Λ)*(low H hH Λ*A*low H hH Λ))*low H hH Δ +
      low H hH Δ*A*high H hH Λ*B*low H hH Δ-
      low H hH Δ*B*high H hH Λ*A*low H hH Δ := by
  let P := low H hH Δ
  let S := low H hH Λ
  have hp : P*S=P := low_nested H hH Δ Λ hΔ
  have hs : S*P=P := by
    have he := congrArg Matrix.conjTranspose hp
    simpa only [Matrix.conjTranspose_mul, P, S, low_hermitian] using he
  have hss : S*S=S := low_square H hH Λ
  have hr (X : Matrix I I ℂ) : P*(S*X)=P*X := by rw [← mul_assoc, hp]
  have ht (X : Matrix I I ℂ) : S*(S*X)=S*X := by rw [← mul_assoc, hss]
  change P*(A*B-B*A)*P = P*((S*A*S)*(S*B*S)-(S*B*S)*(S*A*S))*P+
    P*A*(1-S)*B*P-P*B*(1-S)*A*P
  noncomm_ring
  simp only [hr, ht, hs]
  abel

/-- Sandwiching a matrix between two copies of a low-energy spectral projector does not increase
its operator norm. -/
theorem low_sandwich_norm (H A : Matrix I I ℂ) (hH : H.IsHermitian) (Δ : ℝ) :
    ‖low H hH Δ*A*low H hH Δ‖ ≤ ‖A‖ := by
  calc
    _ ≤ (‖low H hH Δ‖*‖A‖)*‖low H hH Δ‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1*‖A‖)*1 := by gcongr <;> exact low_norm H hH Δ
    _ = _ := by ring

/-- For ordered cutoffs, the norm of the lower-cutoff commutator is bounded by twice the product
of the higher-cutoff factor norms and the two cross-subspace norm products. -/
theorem nested_cutoff_commutator_norm (H : Matrix I I ℂ) (hH : H.IsHermitian)
    (Δ Λ : ℝ) (hΔ : Δ ≤ Λ) (A B : Matrix I I ℂ) :
    ‖low H hH Δ*(A*B-B*A)*low H hH Δ‖ ≤
      2*‖low H hH Λ*A*low H hH Λ‖*‖low H hH Λ*B*low H hH Λ‖+
      ‖low H hH Δ*A*high H hH Λ‖*‖high H hH Λ*B*low H hH Δ‖+
      ‖low H hH Δ*B*high H hH Λ‖*‖high H hH Λ*A*low H hH Δ‖ := by
  let P := low H hH Δ
  let S := low H hH Λ
  let Q := high H hH Λ
  let C := (S*A*S)*(S*B*S)-(S*B*S)*(S*A*S)
  have hQ : Q*Q=Q := high_square H hH Λ
  have hAB : P*A*Q*B*P=(P*A*Q)*(Q*B*P) := by
    calc
      _=P*A*(Q*Q)*B*P := by rw [hQ]
      _=_ := by noncomm_ring
  have hBA : P*B*Q*A*P=(P*B*Q)*(Q*A*P) := by
    calc
      _=P*B*(Q*Q)*A*P := by rw [hQ]
      _=_ := by noncomm_ring
  have hC : ‖P*C*P‖ ≤ 2*‖S*A*S‖*‖S*B*S‖ := by
    calc
      _ ≤ ‖C‖ := low_sandwich_norm H C hH Δ
      _ ≤ ‖(S*A*S)*(S*B*S)‖+‖(S*B*S)*(S*A*S)‖ := norm_sub_le _ _
      _ ≤ ‖S*A*S‖*‖S*B*S‖+‖S*B*S‖*‖S*A*S‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = _ := by ring
  rw [nested_cutoff_commutator H hH Δ Λ hΔ]
  change ‖P*C*P+P*A*Q*B*P-P*B*Q*A*P‖ ≤ _
  rw [hAB, hBA]
  calc
    _ ≤ (‖P*C*P‖+‖(P*A*Q)*(Q*B*P)‖)+‖(P*B*Q)*(Q*A*P)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (2*‖S*A*S‖*‖S*B*S‖+‖P*A*Q‖*‖Q*B*P‖)+‖P*B*Q‖*‖Q*A*P‖ := by
      exact add_le_add (add_le_add hC (norm_mul_le (P*A*Q) (Q*B*P)))
        (norm_mul_le (P*B*Q) (Q*A*P))
    _ = _ := rfl
end Qatlib.Foundations.MatrixGeometry.SpectralCutoff
