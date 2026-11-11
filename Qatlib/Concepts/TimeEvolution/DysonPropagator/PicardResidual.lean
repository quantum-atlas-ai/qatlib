/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel

/-!
# Residual bounds for approximate matrix evolutions

For a matrix function satisfying `Y' = R - A * Y`, `residual_identity` represents its deviation
from the exact constant-generator evolution as an integral of the residual `R`. Contractive and
exponentially damped estimates turn a uniform residual bound into a global error bound. For
background, see [ReedSimon1980I].

## Main statements

* `residual_identity`: variation-of-constants formula for the residual.
* `norm_residual_error_le`: integrated damping bound for the evolution error.

## References

* [Reed and Simon, 1980][ReedSimon1980I]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.TimeEvolution.DysonPropagator.PicardResidual

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
open Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel

variable {I : Type} [Fintype I] [DecidableEq I]

/-- If `Y' = R - A * Y` and `R` is continuous, the error `Y t - evolution A t * Y 0` is the
integral of `evolution A (t - s) * R s`. -/
theorem residual_identity (A : Matrix I I ℂ) (Y R : ℝ → Matrix I I ℂ)
    (hY : ∀ s, HasDerivAt Y (R s - A * Y s) s) (hR : Continuous R) (t : ℝ) :
    Y t - evolution A t * Y 0 =
      ∫ s in 0..t, evolution A (t - s) * R s := by
  have hE (s : ℝ) : HasDerivAt (fun u => evolution A (t - u))
      (evolution A (t - s) * A) s := by
    simpa [evolution, neg_sub] using!
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) A (s - t)).scomp s
        ((hasDerivAt_id s).sub_const t)
  have hd (s : ℝ) : HasDerivAt (fun u => evolution A (t - u) * Y u)
      (evolution A (t - s) * R s) s := by
    convert! (hE s).mul (hY s) using 1
    noncomm_ring
  have hcE : Continuous (fun s => evolution A (t - s)) :=
    continuous_iff_continuousAt.mpr fun s => (hE s).continuousAt
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    ((hcE.mul hR).intervalIntegrable 0 t)
  simpa using! hi.symm

/-- A residual bounded by `δ` on `[0, t]` gives error at most `damping γ t * δ` when the shifted
generator has positive semidefinite Hermitian part. -/
theorem norm_residual_error_le (A : Matrix I I ℂ) (γ δ : ℝ)
    (hA : ((A - γ • (1 : Matrix I I ℂ)) +
      (A - γ • (1 : Matrix I I ℂ))ᴴ).PosSemidef)
    (Y R : ℝ → Matrix I I ℂ)
    (hY : ∀ s, HasDerivAt Y (R s - A * Y s) s) (hR : Continuous R)
    {t : ℝ} (ht : 0 ≤ t)
    (hbound : ∀ s ∈ Set.Icc 0 t, ‖R s‖ ≤ δ) :
    ‖Y t - evolution A t * Y 0‖ ≤ damping γ t * δ := by
  rw [residual_identity A Y R hY hR t]
  have hb (s : ℝ) (hs : s ∈ Set.Ioc 0 t) :
      ‖evolution A (t - s) * R s‖ ≤ Real.exp (-γ * (t - s)) * δ := by
    exact (norm_mul_le _ _).trans
      (mul_le_mul (norm_evolution_le_exp A γ hA (sub_nonneg.mpr hs.2))
        (hbound s ⟨hs.1.le, hs.2⟩) (norm_nonneg _) (Real.exp_pos _).le)
  have hc : Continuous (fun s : ℝ => Real.exp (-γ * (t - s)) * δ) := by fun_prop
  calc
    _ ≤ ∫ s in 0..t, Real.exp (-γ * (t - s)) * δ :=
      intervalIntegral.norm_integral_le_of_norm_le ht
        (Filter.Eventually.of_forall hb) (hc.intervalIntegrable 0 t)
    _ = damping γ t * δ := by
      rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_comp_sub_left (fun s : ℝ => Real.exp (-γ * s)) t]
      simp only [sub_self, sub_zero]
      rw [integral_exp_neg_mul]

/-- For a generator with positive semidefinite Hermitian part, a residual bounded by `δ` on `[0,
t]` gives error at most `t * δ`. -/
theorem norm_residual_error_le_time (A : Matrix I I ℂ)
    (hA : (A + Aᴴ).PosSemidef) (Y R : ℝ → Matrix I I ℂ)
    (hY : ∀ s, HasDerivAt Y (R s - A * Y s) s) (hR : Continuous R)
    {t δ : ℝ} (ht : 0 ≤ t)
    (hbound : ∀ s ∈ Set.Icc 0 t, ‖R s‖ ≤ δ) :
    ‖Y t - evolution A t * Y 0‖ ≤ t * δ := by
  simpa [damping] using! norm_residual_error_le A 0 δ (by simpa using! hA)
    Y R hY hR ht hbound

end Qatlib.Concepts.TimeEvolution.DysonPropagator.PicardResidual
