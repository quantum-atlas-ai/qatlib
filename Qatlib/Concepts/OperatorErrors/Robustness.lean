/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.Basic
import Qatlib.Concepts.CoherentSim.CoherentOAA.QSVT

/-!
# Oracle perturbation bounds for phase words

Alternating phase words built from unitary oracles and orthogonal projectors are Lipschitz in
the oracle matrix, with constant equal to the phase list length. The same estimate survives
compression by isometries, providing a robustness bound for the polynomial transformation
setting of [GilyenSuLowWiebe2019]

## Main statements

* `contractive_product_error`: bounds a product difference with contractive outer factors.
* `phasedAlternating_oracle_error`: bounds phase word error by oracle error times word length.
* `compress_phasedAlternating_oracle_error`: gives the corresponding compressed estimate.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.PhaseGeometry.Phase

namespace Qatlib.Concepts.OperatorErrors.Robustness

open Matrix
open scoped Matrix.Norms.L2Operator

end Qatlib.Concepts.OperatorErrors.Robustness

namespace Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open Matrix
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib
open Qatlib
open Qatlib
open scoped Matrix.Norms.L2Operator

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- If `A` and `D` have norm at most one, then `‖A * B - C * D‖ ≤ ‖B - D‖ + ‖A - C‖`. -/
theorem contractive_product_error (A B C D : Matrix H H ℂ)
    (hA : ‖A‖ ≤ 1) (hD : ‖D‖ ≤ 1) :
    ‖A * B - C * D‖ ≤ ‖B - D‖ + ‖A - C‖ := by
  have he : A * B - C * D = A * (B - D) + (A - C) * D := by
    noncomm_ring
  rw [he]
  calc
    ‖A * (B - D) + (A - C) * D‖ ≤ ‖A * (B - D)‖ + ‖(A - C) * D‖ :=
      norm_add_le _ _
    _ ≤ ‖A‖ * ‖B - D‖ + ‖A - C‖ * ‖D‖ :=
      add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
    _ ≤ 1 * ‖B - D‖ + ‖A - C‖ * 1 :=
      add_le_add (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hD (norm_nonneg _))
    _ = ‖B - D‖ + ‖A - C‖ := by ring

/-- For unitary oracles, orthogonal projectors, and unit modulus phases, replacing `U` by `V`
changes the alternating phase word by at most `zs.length * ‖U - V‖` in operator norm. -/
theorem phasedAlternating_oracle_error {U V P Q : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hV : V ∈ Matrix.unitaryGroup H ℂ)
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    {base : ℂ} (hb : IsPhase base) (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) :
    ‖phasedAlternating U P Q base zs - phasedAlternating V P Q base zs‖ ≤
      (zs.length : ℝ) * ‖U - V‖ := by
  induction zs generalizing U V P Q with
  | nil => simp [phasedAlternating]
  | cons z zs ih =>
    have hz : IsPhase z := hzs z (by simp)
    have hzs' : ∀ w ∈ zs, IsPhase w :=
      fun w hw => hzs w (List.mem_cons_of_mem z hw)
    have hg := phaseRotation_unitary hQ hz
    have hhead : ‖phaseRotation Q z * U‖ ≤ 1 :=
      unitary_norm_le_one ((Matrix.unitaryGroup H ℂ).mul_mem hg hU)
    have htailV : ‖phasedAlternating Vᴴ Q P base zs‖ ≤ 1 :=
      unitary_norm_le_one (phasedAlternating_unitary (adjoint_unitary hV) hQ hP hb zs hzs')
    have hheadError : ‖phaseRotation Q z * U - phaseRotation Q z * V‖ ≤ ‖U - V‖ := by
      rw [← Matrix.mul_sub]
      calc
        ‖phaseRotation Q z * (U - V)‖ ≤ ‖phaseRotation Q z‖ * ‖U - V‖ :=
          Matrix.l2_opNorm_mul _ _
        _ ≤ 1 * ‖U - V‖ :=
          mul_le_mul_of_nonneg_right (unitary_norm_le_one hg) (norm_nonneg _)
        _ = ‖U - V‖ := one_mul _
    have htail := ih (adjoint_unitary hU) (adjoint_unitary hV) hQ hP hzs'
    have hadj : ‖Uᴴ - Vᴴ‖ = ‖U - V‖ := by
      rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
    rw [hadj] at htail
    calc
      ‖phasedAlternating U P Q base (z :: zs) -
          phasedAlternating V P Q base (z :: zs)‖ ≤
          ‖phasedAlternating Uᴴ Q P base zs - phasedAlternating Vᴴ Q P base zs‖ +
            ‖phaseRotation Q z * U - phaseRotation Q z * V‖ :=
        contractive_product_error _ _ _ _ hhead htailV
      _ ≤ (zs.length : ℝ) * ‖U - V‖ + ‖U - V‖ := add_le_add htail hheadError
      _ = ((z :: zs).length : ℝ) * ‖U - V‖ := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring

/-- Compressing the two alternating phase words by isometries preserves the bound `zs.length *
‖U - V‖`. -/
theorem compress_phasedAlternating_oracle_error
    {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (hL : IsIsometry L) (hR : IsIsometry R)
    {U V P Q : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hV : V ∈ Matrix.unitaryGroup H ℂ)
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    {base : ℂ} (hb : IsPhase base) (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) :
    ‖compress L (phasedAlternating U P Q base zs) R -
        compress L (phasedAlternating V P Q base zs) R‖ ≤
      (zs.length : ℝ) * ‖U - V‖ :=
  (compress_sub_norm_le hL hR _ _).trans
    (phasedAlternating_oracle_error hU hV hP hQ hb zs hzs)

end Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
