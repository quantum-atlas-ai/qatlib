/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Reflections.ReflectionsPhaseBridge

set_option backward.isDefEq.respectTransparency false

/-!
# Reichardt 2010 — Algorithm 3, the bare-power test (model)

Fixed source: Ben W. Reichardt, *Reflections for quantum query algorithms*,
arXiv:1005.1601v1, Section 2, third algorithm (p. 5), analysed in Proposition 3.6
(p. 9).

The third source algorithm prepares the root state `|0⟩`, picks `T ∈ [⌈10⁵W⌉]`
uniformly at random, applies the two-reflection unitary `U_x^T`, and accepts when
the measurement of the vertex register returns the root `|0⟩`.  Its acceptance
probability is therefore the source quantity

`p₁ = E_{T∈[τ]} |⟨0|U_x^T|0⟩|²`, with `τ = ⌈10⁵W⌉`,

the `|0⟩` Born probability of `U_x^T|0⟩` averaged uniformly over the horizon.
This module fixes exactly that objective; the analysis is in `BarePowerTest`.

* `barePowerState` — step 2 of the algorithm on the chosen power `T = t + 1`.
* `barePowerScore` — step 3: the uniform average of the `|0⟩` Born probability,
  i.e. the acceptance probability `p₁` of source Algorithm 3.

The model is stated for an arbitrary finite-dimensional unitary; the paper-layer
instance is `twoReflectionUnitary input f x Δ` on `Vertex X f n m` with the root
vertex `Sum.inr (Sum.inl ())` as `|0⟩`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ReflectQuery10.MainResults

open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath

variable {J : Type} [Fintype J] [DecidableEq J]

/-- Step 2 of source Algorithm 3 on the chosen power `T = t + 1`: the powered root
state `U^T |0⟩`.  The horizon `τ` is the range of the uniform choice of `T`. -/
def barePowerState (U : Matrix J J ℂ) (z : J) {τ : ℕ} (t : Fin τ) : QState J :=
  U ^ (t.val + 1) *ᵥ Ket z

/-- Step 3 of source Algorithm 3: its acceptance probability, i.e. the `|0⟩` Born
probability `|⟨0|U^T|0⟩|²` averaged uniformly over the horizon `T ∈ [τ]`.

For the empty horizon the average is the empty sum, hence `0`; every consumer
carries `0 < τ` (the source schedule `τ = ⌈10⁵W⌉` is positive because `W ≥ 1`). -/
noncomputable def barePowerScore (U : Matrix J J ℂ) (z : J) (τ : ℕ) : ℝ :=
  (τ : ℝ)⁻¹ * ∑ t : Fin τ, ‖barePowerState U z t z‖ ^ 2

/-- The bare-power acceptance probability is the uniform average of the individual
`|0⟩` Born probabilities.  This is the literal reading of steps 2 and 3 of the
source algorithm and is the form both bounds consume. -/
theorem barePowerScore_eq_sum (U : Matrix J J ℂ) (z : J) (τ : ℕ) :
    barePowerScore U z τ = (τ : ℝ)⁻¹ * ∑ t : Fin τ, ‖barePowerState U z t z‖ ^ 2 :=
  rfl

end Qatlib.Papers.ReflectQuery10.MainResults
