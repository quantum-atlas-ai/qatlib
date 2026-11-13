/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProjectorQAOA26.FeasibleGap.CrossingUpper
import Qatlib.Papers.ProjectorQAOA26.FeasibleGap.EC3ModelBridge

/-!
# Minimum-gap bounds for the uniform EC3 interpolation

The theorem `ec3_uniform_minimumGap_bounds` specializes the bounded-cost minimum-gap estimates
to exact-cover-by-three instances with m disjoint feasible triples, f free bits, and r remaining
clauses. Under unique satisfiability and the stated size condition, the feasible dimension L =
3^m 2^f gives explicit lower and upper bounds on the minimum gap [ZhouAnLiu2026].

## Main statements

* `ec3_uniform_minimumGap_bounds`: The actual feasible interpolation has minimum gap between 1 /
  (8(4r + 1)√L) and 4 / √L.

## References

* [Zhou et al., 2026][ZhouAnLiu2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ProjectorQAOA26.FeasibleGap
open scoped Classical
open Qatlib.Papers.ProjectorQAOA26.StageStability

/-- For the stated uniquely satisfiable EC3 instance with `r ≥ 1`, feasible dimension `L = 3^m *
2^f ≥ 2`, and `L ≥ 1 + 16 * (4r)²`, the feasible interpolation's minimum gap lies between `1
/ (8 * (4r + 1) * sqrt L)` and `4 / sqrt L` [ZhouAnLiu2026]. -/
theorem ec3_uniform_minimumGap_bounds (m f r : ℕ)
    (clauses : Fin r → Fin 3 → ((Fin m × Fin 3) ⊕ Fin f))
    (zero : EC3Feasible m f)
    (hunique : ∀ g : ((Fin m × Fin 3) ⊕ Fin f) → Bool,
      ((∀ c : Fin m,ec3SatB (fun j => g (Sum.inl (c,j)))=true) ∧
        ∀ c : Fin r,ec3SatB (fun j => g (clauses c j))=true) ↔ g=zero.1)
    (hr : 1≤r) (hL : 2≤Fintype.card (EC3Feasible m f))
    (hlarge : 1+16*(4*(r:ℝ))^2≤(3:ℝ)^m*(2:ℝ)^f) :
    1/(8*(4*(r:ℝ)+1)*Real.sqrt ((3:ℝ)^m*(2:ℝ)^f)) ≤
        minimumGap (fun g : EC3Feasible m f => ec3Cost r clauses g.1) hL ∧
      minimumGap (fun g : EC3Feasible m f => ec3Cost r clauses g.1) hL ≤
        4/Real.sqrt ((3:ℝ)^m*(2:ℝ)^f) := by
  letI : Nonempty (EC3Feasible m f) := ⟨zero⟩
  have hu : ∀ g : EC3Feasible m f,
      (∀ c,ec3SatB (fun j => g.1 (clauses c j))=true) ↔ g=zero := by
    intro g
    constructor
    · intro hg
      exact Subtype.ext ((hunique g.1).mp ⟨g.2,hg⟩)
    · intro hg
      subst g
      exact ((hunique zero.1).mpr rfl).2
  obtain ⟨hz,he⟩ := ec3Cost_unique_bounds r clauses zero hu
  have hcard : (Fintype.card (EC3Feasible m f):ℝ)=(3:ℝ)^m*(2:ℝ)^f := by
    rw [card_EC3Feasible]
    push_cast
    rfl
  have hl : 1+16*(4*(r:ℝ))^2≤(Fintype.card (EC3Feasible m f):ℝ) := by rw [hcard];exact hlarge
  have hh := actual_minimumGap_bounds
    (fun g : EC3Feasible m f => ec3Cost r clauses g.1) zero hz (4*(r:ℝ))
    (by
      have hrr : (1:ℝ)≤r := by exact_mod_cast hr
      linarith) he hL hl
  simpa only [hcard] using! hh

end Qatlib.Papers.ProjectorQAOA26.FeasibleGap
