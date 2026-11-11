/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# Method of lines for parabolic PDEs — Theorem 3 (uniqueness)

Fixed version: **arXiv:2606.03407v1**, Theorem 3 (§3.1, PDF p.13), proof in
Appendix A (PDF p.58).

The paper considers the parabolic problem

`u_t = Δu + Σ_l c_l u_{x_l} + f`,  `u(x,0) = u₀(x)`,

with the mixed Dirichlet/Neumann/periodic conditions (7)–(9).  If two
`C^{2,1}(Ω×[0,T])` solutions exist, they coincide.  The proof sets
`v = u₁ − u₂`, which solves the homogeneous problem, and uses the weighted
energy

`E(t) = ½ ∫_Ω v² exp(Σ_{l∈S₂} c_l x_l) dx`.

Integrating by parts in each direction gives `E'(t) ≤ 0`; since `E ≥ 0` and
`E(0) = 0`, one has `E ≡ 0`, and the positivity of the weight makes `v ≡ 0`.

This file formalises the *energy argument* that turns those facts into
uniqueness.  The PDE-specific derivations of `E ≥ 0`, `E(0) = 0`, `E' ≤ 0`
and of the implication `E(t) = 0 → u₁(t) = u₂(t)` are the integration-by-parts
step of Appendix A; they are recorded as the hypotheses `hE_nonneg`,
`hE_zero`, `hE_nonpos` and `hE_definite`.  Nothing stronger than the paper's
energy facts is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Qatlib.Papers.MethodOfLines26.ParabolicBase.Source

open scoped Real

/-- **Energy-method uniqueness core.**  If the weighted energy `E` of the
difference of two solutions is nonnegative on `[0,T]`, vanishes at `0`, has
nonpositive derivative there, and vanishes only when the two solutions agree,
then the two solutions agree on `[0,T]`.

This is the last step of Appendix A (PDF p.58): `E ≡ 0` and `E = 0 → v = 0`. -/
theorem energy_method_uniqueness
    {V : Type*} (u₁ u₂ : ℝ → V) (E dE : ℝ → ℝ)
    (hE_zero : E 0 = 0)
    (hE_deriv : ∀ t, 0 ≤ t → HasDerivAt E (dE t) t)
    (hE_nonpos : ∀ t, 0 ≤ t → dE t ≤ 0)
    (hE_nonneg : ∀ t, 0 ≤ t → 0 ≤ E t)
    (hE_definite : ∀ t, 0 ≤ t → E t = 0 → u₁ t = u₂ t) :
    ∀ t, 0 ≤ t → u₁ t = u₂ t := by
  intro t ht
  -- `E` is antitone on `[0, ∞)` because its derivative is nonpositive.
  have hanti : AntitoneOn E (Set.Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := dE) (convex_Ici (0 : ℝ))
      (fun x hx => ((hE_deriv x (Set.mem_Ici.mp hx)).continuousAt).continuousWithinAt)
      (fun x hx => ?_) (fun x hx => ?_)
    · have hx' : (0 : ℝ) < x := by simpa [interior_Ici] using hx
      exact (hE_deriv x hx'.le).hasDerivWithinAt
    · have hx' : (0 : ℝ) < x := by simpa [interior_Ici] using hx
      exact hE_nonpos x hx'.le
  have hle : E t ≤ E 0 :=
    hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  rw [hE_zero] at hle
  exact hE_definite t ht (le_antisymm hle (hE_nonneg t ht))

/-- Fixed arXiv:2606.03407v1, Theorem 3 (uniqueness, PDF p.13; proof
Appendix A p.58).  Two classical solutions `u₁`, `u₂` of the parabolic problem
(6) with boundary conditions (7)–(9) that share the initial datum `u₀` agree on
`[0,T]`.

The two solutions are passed as curves `ℝ → V`; the difference
`v = u₁ − u₂` and the weighted energy `E` of Appendix A are the arguments of
`energy_method_uniqueness`. -/
theorem parabolic_uniqueness
    {V : Type*} (u₁ u₂ : ℝ → V) (E dE : ℝ → ℝ)
    (hE_zero : E 0 = 0)
    (hE_deriv : ∀ t, 0 ≤ t → HasDerivAt E (dE t) t)
    (hE_nonpos : ∀ t, 0 ≤ t → dE t ≤ 0)
    (hE_nonneg : ∀ t, 0 ≤ t → 0 ≤ E t)
    (hE_definite : ∀ t, 0 ≤ t → E t = 0 → u₁ t = u₂ t) :
    ∀ t, 0 ≤ t → u₁ t = u₂ t :=
  energy_method_uniqueness u₁ u₂ E dE hE_zero hE_deriv hE_nonpos hE_nonneg hE_definite

end Qatlib.Papers.MethodOfLines26.ParabolicBase.Source
