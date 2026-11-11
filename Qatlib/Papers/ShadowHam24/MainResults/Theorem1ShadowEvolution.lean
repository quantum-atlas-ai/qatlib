/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ShadowHam24.MainResults.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 1 (arXiv:2407.21775, p. 3, Eq. (4))

The shadow state obeys the Schrödinger equation
`d/dt |ρ(t);S⟩ = -i H_S |ρ(t);S⟩` whenever `ρ(t)` solves the von Neumann
equation `dρ/dt = -i[H,ρ]` and `(H,S)` satisfies the invariance property.

The proof follows Supplementary Note 1, Eqs. (16)–(18): differentiate the
amplitude `⟨O_m(t)⟩ = tr(ρ(t) O_m)`, use `dρ/dt = -i[H,ρ]` and cyclicity of the
trace, then apply the IP.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.Frobenius

namespace Qatlib.Papers.ShadowHam24.MainResults

variable {N M : Type*} [Fintype N] [DecidableEq N] [Fintype M] [DecidableEq M]

/-- **Theorem 1** (paper p. 3, Eq. (4)): given a differentiable density
trajectory satisfying the von Neumann equation at `t`, and an invariance
property `[H,O_m] = -∑_{m'} h_{mm'} O_{m'}`, the (unnormalised) shadow state
vector evolves as `d/dt |ρ(t);S⟩ = -i H_S |ρ(t);S⟩`. -/
theorem shadowState_evolution (ρ : ℝ → Matrix N N ℂ) (H : Matrix N N ℂ)
    (O : M → Matrix N N ℂ) (hS : Matrix M M ℂ) (t : ℝ)
    (hρ : HasDerivAt ρ ((-(Complex.I)) • (H * ρ t - ρ t * H)) t)
    (hip : InvarianceProperty H O hS) :
    HasDerivAt (fun s => shadowState (ρ s) O)
      ((-(Complex.I)) • (hS *ᵥ shadowState (ρ t) O)) t := by
  rw [hasDerivAt_pi]
  intro m
  -- differentiate the m-th amplitude
  have h1 : HasDerivAt (fun s => (ρ s * O m).trace)
      (((-(Complex.I)) • (H * ρ t - ρ t * H)) * O m).trace t :=
    hasDerivAt_trace_mul_const ρ _ (O m) t hρ
  have h2 : (((-(Complex.I)) • (H * ρ t - ρ t * H)) * O m).trace
      = Complex.I * (ρ t * (H * O m - O m * H)).trace :=
    trace_vonNeumann_mul (ρ t) H (O m)
  rw [h2] at h1
  rw [hip m] at h1
  rw [trace_mul_neg_sum_smul] at h1
  -- identify the right-hand side with `(-i) (H_S v)_m`
  have htarget : ((-(Complex.I)) • (hS *ᵥ shadowState (ρ t) O)) m
      = Complex.I * (- ∑ m', hS m m' * (ρ t * O m').trace) := by
    simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, shadowState, expectation]
    ring
  rw [htarget]
  simpa [shadowState, expectation] using h1

end Qatlib.Papers.ShadowHam24.MainResults
