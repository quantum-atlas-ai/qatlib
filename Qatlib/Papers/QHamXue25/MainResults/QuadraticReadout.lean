/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QHamXue25.NSDualLift.Linearization

@[expose] public section

/-!
# Quadratic lift readout

Freeze the first auxiliary location and differentiate in the spatial direction of the
second location. Restricting back to the diagonal gives the quadratic Burgers term.
-/

set_option autoImplicit false



namespace Qatlib.Papers.QHamXue25.MainResults

/-- The lifted quadratic variable has one auxiliary space-time point per factor. -/
def pair (f g : ℝ × ℝ → ℝ) (p : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ := f p.1 * g p.2

/-- The spatial derivative of the diagonal readout acts on the second factor. -/
theorem eq27_readout (f g : ℝ × ℝ → ℝ) (x t : ℝ)
    {g' : (ℝ × ℝ) →L[ℝ] ℝ} (dg : HasFDerivAt g g' (x, t)) :
    HasDerivAt (fun s => pair f g ((x, t), (s, t))) (f (x, t) * g' (1, 0)) x := by
  have hpath : HasFDerivAt (fun s : ℝ => (s, t)) (ContinuousLinearMap.inl ℝ ℝ ℝ) x :=
    hasFDerivAt_prodMk_left x t
  have hcomp : HasFDerivAt (g ∘ (fun s : ℝ => (s, t)))
      (g'.comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) x :=
    HasFDerivAt.comp (hg := dg) (hf := hpath)
  have hslice : HasDerivAt (fun s : ℝ => g (s, t)) (g' (1, 0)) x :=
    HasFDerivAt.hasDerivAt hcomp
  exact hslice.const_mul (f (x, t))

/-- With the first factor negated, the Burgers lift reads back as `-u ∂ₓu`. -/
theorem burgers_quadratic_readout (u : ℝ × ℝ → ℝ) (x t : ℝ)
    {u' : (ℝ × ℝ) →L[ℝ] ℝ} (du : HasFDerivAt u u' (x, t)) :
    HasDerivAt (fun s => pair (fun p => -u p) u ((x, t), (s, t)))
      (-u (x, t) * u' (1, 0)) x := eq27_readout _ u x t du

end Qatlib.Papers.QHamXue25.MainResults
