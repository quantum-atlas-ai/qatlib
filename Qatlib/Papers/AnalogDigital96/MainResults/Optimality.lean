/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.ContinuousAdv

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Qatlib.Concepts.QueryComplexity.ContinuousAdv
namespace Qatlib.Papers.AnalogDigital96.MainResults.Optimality
variable {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem source_sum_separation_lower [Nonempty ι]
    (b : OrthonormalBasis ι ℂ V) {E ε T : ℝ} (hE : 0 < E) (hε : 0 ≤ ε)
    (HD : ℝ → V →L[ℂ] V) (hHD : ∀ t u v, inner ℂ ((HD t) u) v = inner ℂ u ((HD t) v))
    (ψw : ι → ℝ → V) (ψ : ℝ → V)
    (hψw_norm : ∀ i t, ‖ψw i t‖ = 1) (hψ_norm : ∀ t, ‖ψ t‖ = 1)
    (h_init : ∀ i, ψw i 0 = ψ 0)
    (hψw : ∀ (i : ι) (t : ℝ),
      HasDerivAt (ψw i) ((-Complex.I) • (rankOneAction b E i (ψw i t) + HD t (ψw i t))) t)
    (hψ : ∀ t, HasDerivAt ψ ((-Complex.I) • (HD t (ψ t))) t)
    (hsep_sum : (Fintype.card ι : ℝ) * ε ≤ ∑ i, ‖ψw i T - ψ T‖ ^ 2) (hT : 0 ≤ T) :
    ε * Real.sqrt (Fintype.card ι) / (2 * E) ≤ T := by
  exact continuous_sum_lower_bound b hE hε HD hHD ψw ψ hψw_norm hψ_norm h_init hψw hψ hsep_sum hT

theorem source_except_one_lower
    (b : OrthonormalBasis ι ℂ V) {E ε T : ℝ} (hE : 0 < E)
    (HD : ℝ → V →L[ℂ] V) (hHD : ∀ t u v, inner ℂ ((HD t) u) v = inner ℂ u ((HD t) v))
    (ψw : ι → ℝ → V) (ψ : ℝ → V)
    (hψw_norm : ∀ i t, ‖ψw i t‖ = 1) (hψ_norm : ∀ t, ‖ψ t‖ = 1)
    (h_init : ∀ i, ψw i 0 = ψ 0)
    (hψw : ∀ (i : ι) (t : ℝ),
      HasDerivAt (ψw i) ((-Complex.I) • (rankOneAction b E i (ψw i t) + HD t (ψw i t))) t)
    (hψ : ∀ t, HasDerivAt ψ ((-Complex.I) • (HD t (ψ t))) t)
    (e : ι) (hsep : ∀ i, i ≠ e → ε ≤ ‖ψw i T - ψ T‖ ^ 2) (hT : 0 ≤ T) :
    ε * ((Fintype.card ι : ℝ) - 1) / (2 * E * Real.sqrt (Fintype.card ι)) ≤ T := by
  exact continuous_except_one_lower_bound b hE HD hHD ψw ψ hψw_norm hψ_norm h_init hψw hψ e hsep hT
end Qatlib.Papers.AnalogDigital96.MainResults.Optimality
