/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ParabolicPDE24.HeatLimit.ModeState
import Qatlib.Papers.ParabolicPDE24.FourierModel.FourierSystem

/-!
# Finite-band heat approximation

`sourceSignal` and `sourceHeat` assemble the Fourier-mode relaxation and heat solutions over a
band of frequencies. Under the stated band and small-parameter conditions, the module transfers
scalar estimates to Euclidean-state error and normalized-state error bounds for the model of
[JinLiu2024].

## Main statements

* `source_uniform_error`: the finite-band error is bounded by a decaying multiple of `ε² * ‖x‖`.
* `source_normalized_error`: nonzero initial data yield a normalized error bounded by `2 *
  bandConstant k A t * ε²`.

## References

* [Jin and Liu, 2024][JinLiu2024]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ParabolicPDE24.HeatLimit
open Qatlib.Papers.ParabolicPDE24.FourierDefs
open Qatlib.Foundations.TimeEvolution.TelegraphLimit

/-- The Euclidean state obtained by evolving each initial Fourier coefficient with `signal` at
its frequency. -/
def sourceSignal {I : Type} (k ε : ℝ) (ω : I→ℝ) (x : EuclideanSpace ℂ I) (t : ℝ) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 (fun i=>signal k ε (ω i) (x i) t)

/-- The Euclidean heat state whose coefficient at frequency `ω i` is multiplied by `heatMode (k
* (ω i)^2) t`. -/
def sourceHeat {I : Type} (k : ℝ) (ω : I→ℝ) (x : EuclideanSpace ℂ I) (t : ℝ) : EuclideanSpace ℂ I :=
  weightedState (fun i=>heatMode (k*(ω i)^2) t) x

/-- The source signal is the weighted initial state with weights `mode (k * ε²) (k * (ω i)^2)
t`. -/
theorem sourceSignal_eq_weighted {I : Type} (k ε : ℝ) (ω : I→ℝ) (x : EuclideanSpace ℂ I) (t : ℝ) :
    sourceSignal k ε ω x t=weightedState (fun i=>mode (k*ε^2) (k*(ω i)^2) t) x := rfl

/-- For positive `k` and `ε`, nonnegative time, frequencies satisfying `4 ≤ (ω i)^2` and `k * (ω
i)^2 ≤ A`, and the stated smallness bound, the source signal error is at most
`uniformConstant k A * ε² * exp (−2 * k * t) * ‖x‖`. See [JinLiu2024]. -/
theorem source_uniform_error {I : Type} [Fintype I] (ω : I→ℝ) (x : EuclideanSpace ℂ I)
    {k ε A t : ℝ} (hk : 0<k) (hε : 0<ε) (hA : 0≤A)
    (hω : ∀i,4≤(ω i)^2 ∧ k*(ω i)^2≤A) (hm : 4*(k*ε^2)*A≤3/4) (ht : 0≤t) :
    ‖sourceSignal k ε ω x t-sourceHeat k ω x t‖≤
      uniformConstant k A*ε^2*Real.exp (-2*k*t)*‖x‖ := by
  rw [sourceSignal_eq_weighted]
  apply physical_uniform_error _ x hk hε _ hA hm ht
  intro i
  exact ⟨by nlinarith [(hω i).1],(hω i).2⟩

/-- For nonzero initial data, positive `k` and `ε`, nonnegative time, and the stated upper band
and smallness bounds, the normalized source heat and signal states differ by at most `2 *
bandConstant k A t * ε²`. See [JinLiu2024]. -/
theorem source_normalized_error {I : Type} [Fintype I] (ω : I→ℝ) (x : EuclideanSpace ℂ I)
    (hx : x≠0) {k ε A t : ℝ} (hk : 0<k) (hε : 0<ε) (hA : 0≤A)
    (hω : ∀i,k*(ω i)^2≤A) (hm : 4*(k*ε^2)*A≤3/4) (ht : 0≤t) :
    ‖Qatlib.Papers.ParabolicPDE24.MainResults.normalizedState (sourceHeat k ω x t)-
      Qatlib.Papers.ParabolicPDE24.MainResults.normalizedState (sourceSignal k ε ω x t)‖≤
      2*bandConstant k A t*ε^2 := by
  rw [sourceSignal_eq_weighted]
  apply physical_normalized_error _ x hx hk hε hA _ hm ht
  intro i
  exact ⟨by positivity,hω i⟩
end Qatlib.Papers.ParabolicPDE24.HeatLimit
