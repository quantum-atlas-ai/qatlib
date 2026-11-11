/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QcaDynamics.ScalarNoGo.FiniteSupport

/-!
# Operator form of the scalar QCA no-go theorem

This module realizes finitely supported scalar weights as a translation-invariant convolution
update and defines its formal adjoint. If composing the update with that adjoint is the identity
on every sequence, the update is a single lattice shift multiplied by a unit-modulus scalar. See
[Meyer1996a].

## Main statements

* `bandedUnitary_of_adjoint_inverse`: If the update composed with its formal adjoint fixes every
  sequence, its weights satisfy `IsBandedUnitary`.
* `noGo_operator`: If the update composed with its formal adjoint is the identity on every
  sequence, the weights are supported at one site with unit-modulus coefficient and the update
  is the corresponding phased shift.

## References

* [Meyer, 1996][Meyer1996a]
-/

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.QcaDynamics.ScalarNoGo

namespace Qatlib.Papers.QCellAutomata96.MainResults

/-- The finite convolution update `∑ e, w e * ψ (x - e)` over the support of `w`. -/
def bandStep (w : ℤ →₀ ℂ) (ψ : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∑ e ∈ w.support, w e * ψ (x - e)

/-- The formal adjoint convolution update using conjugate weights and the translated values `ψ
(x + e)`. -/
def bandAdjointStep (w : ℤ →₀ ℂ) (ψ : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∑ e ∈ w.support, star (w e) * ψ (x + e)

/-- The finite convolution update commutes with every integer translation. See [Meyer1996a]. -/
theorem bandStep_translation (w : ℤ →₀ ℂ) (ψ : ℤ → ℂ) (k x : ℤ) :
    bandStep w (fun y => ψ (y - k)) x = bandStep w ψ (x - k) := by
  unfold bandStep
  apply Finset.sum_congr rfl
  intro e _
  change w e * ψ (x - e - k) = w e * ψ (x - k - e)
  have h : x - e - k = x - k - e := by omega
  rw [h]

/-- Applying the update and its formal adjoint to the delta sequence gives the autocorrelation
of the weights. See [Meyer1996a]. -/
theorem bandStep_adjoint_delta (w : ℤ →₀ ℂ) (d : ℤ) :
    bandStep w (bandAdjointStep w (fun y => if y = 0 then 1 else 0)) d =
      autocorr w d := by
  unfold bandStep bandAdjointStep
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold autocorr
  apply Finset.sum_congr rfl
  intro m _
  have heq : ∀ e : ℤ, d - e + m = 0 ↔ e = m + d := by omega
  simp_rw [heq]
  rw [Finset.sum_eq_single (m + d)]
  · simp
  · intro e _ he
    simp [he]
  · intro he
    have hz : w (m + d) = 0 := Finsupp.notMem_support_iff.mp he
    simp [hz]

/-- If the update composed with its formal adjoint fixes every sequence, its weights satisfy
`IsBandedUnitary`. -/
theorem bandedUnitary_of_adjoint_inverse (w : ℤ →₀ ℂ)
    (hU : ∀ ψ : ℤ → ℂ, bandStep w (bandAdjointStep w ψ) = ψ) :
    IsBandedUnitary w := by
  intro d
  rw [← bandStep_adjoint_delta]
  exact congrFun (hU (fun y => if y = 0 then 1 else 0)) d

/-- If the update composed with its formal adjoint is the identity on every sequence, the
weights are supported at one site with unit-modulus coefficient and the update is the
corresponding phased shift. See [Meyer1996a]. -/
theorem noGo_operator (w : ℤ →₀ ℂ)
    (hU : ∀ ψ : ℤ → ℂ, bandStep w (bandAdjointStep w ψ) = ψ) :
    ∃ (k : ℤ) (c : ℂ), ‖c‖ = 1 ∧ w = c • Finsupp.single k 1 ∧
      ∀ (ψ : ℤ → ℂ) (x : ℤ), bandStep w ψ x = c * ψ (x - k) := by
  obtain ⟨k, c, hc, hw⟩ := noGo_lemma w (bandedUnitary_of_adjoint_inverse w hU)
  refine ⟨k, c, hc, hw, ?_⟩
  intro ψ x
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  rw [hw]
  simp [bandStep, Finsupp.support_single, hc0]

end Qatlib.Papers.QCellAutomata96.MainResults
