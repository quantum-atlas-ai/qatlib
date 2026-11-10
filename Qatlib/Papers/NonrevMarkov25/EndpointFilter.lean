/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PolynomialCalc.EndpointFilter
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Papers.NonrevMarkov25.EndpointFilter

theorem source_per_instance (δ ε : ℝ) (hδ0 : 0<δ) (hδ1 : δ<1) (hε0 : 0<ε) (hε1 : ε<1) :
    ∃ c : ℝ,0<c ∧ c<1 ∧ ∃ C : ℝ,0<C ∧ ∃ p : Polynomial ℝ,
      (p.natDegree : ℝ)≤C*Real.rpow δ (-(1/2 : ℝ))*Real.log (1/ε) ∧
      (∀ x : ℝ,-1≤x → x≤1 → |p.eval x|≤1) ∧
      (∀ x : ℝ,-1≤x → x≤1-δ → |p.eval x|≤ε) ∧
      (∀ x : ℝ,1-c*δ≤x → x≤1 → 1-ε≤p.eval x) :=
  Qatlib.Concepts.PolynomialCalc.EndpointFilter.per_instance_filter δ ε hδ0 hδ1 hε0 hε1
end Qatlib.Papers.NonrevMarkov25.EndpointFilter
