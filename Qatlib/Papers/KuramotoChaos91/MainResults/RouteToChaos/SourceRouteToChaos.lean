/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KuramotoChaos91.MainResults.KSSetting

set_option backward.isDefEq.respectTransparency false

/-!
# The route to chaos for the Kuramoto–Sivashinsky equation (claim c001)

Source: D. T. Papageorgiou and Y. S. Smyrlis, *The route to chaos for the
Kuramoto–Sivashinsky equation*, Theoretical and Computational Fluid Dynamics
**3** (1991), pp. 15–42, DOI `10.1007/BF00271514`.  Bibliographic reference: the journal version; the available local
report and extracted Markdown have not established version equivalence.  Claim `c001` of
`metadata/papers/KuramotoChaos91.json` is the abstract sentence (extract
line 15; p. 15) describing the ordered windows that the numerical experiments
establish as the viscosity decreases.

The provisional vocabulary below encodes the reported sequence using
`...MainResults.KSSetting`: a single Kuramoto–Sivashinsky experiment (all
runs from `u₀(x) = -sin x` on the `2π`-periodic domain) together with ten
viscosity windows, ordered by decreasing viscosity, in which the asymptotic
solution runs through

`fully modal → bimodal → fully modal → trimodal → time periodic → fully modal
→ time periodic → tetramodal → period-doubling cascade → chaos`.

No dynamical existence theorem is established here. Only the finite sequence
and its order-theoretic consequences are proved; these do not cover c001.
-/

set_option autoImplicit false

namespace Qatlib.Papers.KuramotoChaos91.MainResults.RouteToChaos

open Qatlib.Papers.KuramotoChaos91.MainResults.KSSetting

/-! ## The paper's regime sequence -/

/-- The regime sequence of the abstract, indexed by the ten stages:
`0` fully modal steady, `1` bimodal steady, `2` fully modal steady,
`3` trimodal steady, `4` time periodic, `5` fully modal steady,
`6` time periodic, `7` tetramodal steady, `8` period-doubling cascade,
`9` chaos.  Source: Papageorgiou–Smyrlis 1991, abstract (p. 15). -/
def routeRegime : Fin 10 → AttractorRegime := fun i =>
  match i.val with
  | 0 => .fullyModalSteady
  | 1 => .bimodalSteady
  | 2 => .fullyModalSteady
  | 3 => .trimodalSteady
  | 4 => .timePeriodic
  | 5 => .fullyModalSteady
  | 6 => .timePeriodic
  | 7 => .tetramodalSteady
  | 8 => .periodDoublingCascade
  | _ => .chaotic

/-- Stage `1` of the route is the bimodal steady attractor.
Source: Papageorgiou–Smyrlis 1991, abstract (p. 15); definitional unfolding of
`routeRegime`. -/
theorem routeRegime_one : routeRegime 1 = .bimodalSteady := rfl

/-- Stage `3` of the route is the trimodal steady attractor.
Source: Papageorgiou–Smyrlis 1991, abstract (p. 15); definitional unfolding of
`routeRegime`. -/
theorem routeRegime_three : routeRegime 3 = .trimodalSteady := rfl

/-- Stage `7` of the route is the tetramodal steady attractor.
Source: Papageorgiou–Smyrlis 1991, abstract (p. 15); definitional unfolding of
`routeRegime`. -/
theorem routeRegime_seven : routeRegime 7 = .tetramodalSteady := rfl

/-- Stage `8` of the route is the period-doubling cascade.
Source: Papageorgiou–Smyrlis 1991, abstract (p. 15); definitional unfolding of
`routeRegime`. -/
theorem routeRegime_eight : routeRegime 8 = .periodDoublingCascade := rfl

/-- Stage `9` of the route is chaos.
Source: Papageorgiou–Smyrlis 1991, abstract (p. 15); definitional unfolding of
`routeRegime`. -/
theorem routeRegime_nine : routeRegime 9 = .chaotic := rfl

/-- There are exactly ten stages in the route, and the four named `k`-modal
stages occur at indices `1`, `3`, `7` (and the cascade at `8`).
Source: Papageorgiou–Smyrlis 1991, abstract (p. 15). -/
theorem routeRegime_stage_count :
    (List.ofFn routeRegime).length = 10 ∧
      routeRegime 1 = .bimodalSteady ∧
      routeRegime 3 = .trimodalSteady ∧
      routeRegime 7 = .tetramodalSteady := by
  refine ⟨rfl, routeRegime_one, routeRegime_three, routeRegime_seven⟩

/-! The dynamical existence claim is unproved. It is deliberately not exported
as a theorem: the provisional vocabulary in `KSSetting` still needs a faithful
bridge to the source's attractors and certified numerical continuation. -/

end Qatlib.Papers.KuramotoChaos91.MainResults.RouteToChaos
