/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.TunableUniversalityLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.AmplificationProductsLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.OptimalThresholdAllocationLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.TunableActualQueryComplexityLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.OptimizedTunableConsumerLows

set_option backward.isDefEq.respectTransparency false

/-!
# SourceAmplificationTheorems — universality, products and query complexity

Low--Su, fixed arXiv:2410.18178v2,
PDF SHA-256 5bc33df5fbcd340bd3381e798bb80a436fdc6596027697440f882c15769de5a6.

Paper Proposition 4 (p.14) is the universality correspondence between Tunable
VTAA and variable-time nested amplitude amplification; Lemma 5 (p.15) is the
query-product representation; Proposition 6 (p.16) is the four-part query
complexity of Tunable VTAA. Each is bridged here to the corresponding frozen
G-goal contract of Frozen v2.0.2, whose proofs are already compiled there.

Boundary: the statements are the frozen contracts verbatim; they presuppose the
known prefix amplitudes and legal stage prices described in the paper and do
not provide an amplitude-estimation program.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Papers.QLSStatePrep24.Amplification

/-- Fixed arXiv:2410.18178v2, Proposition 4 (p.14): every Tunable VTAA whose
thresholds satisfy `α_j ≤ 1` and `Σ_j α_j = O(1)` is a variable-time nested
amplitude amplification, and conversely the nested construction yields such a
tunable schedule. This is the frozen contract
`Clause8TunableUniversality` proved by `Clause8TunableUniversality_answer`. -/
theorem prop4_tunable_universality : Clause8TunableUniversality :=
  Clause8TunableUniversality_answer

/-- Fixed arXiv:2410.18178v2, Lemma 5 (p.15): the query product of the nested
amplification word equals the product of `(2 r_j + 1)` over the nontrivial
stages, the paid cost of one more stage is `(2r+1)` times the previous cost
plus that stage's price, and the final success amplitude equals
`postAmplitude = plainAmplitude * totalLoss * ∏ (2r_j+1)`. This is the frozen
contract `Clause9AmplificationProducts` proved by `Clause9AmplificationProducts_answer`. -/
theorem lemma5_query_product_representation : Clause9AmplificationProducts :=
  Clause9AmplificationProducts_answer

/-- Fixed arXiv:2410.18178v2, Proposition 6 (p.16): (i) the number of
nontrivial stages is `O(log_3(1/√p_succ))` and the paid slot-0 query count is
at most `(6/5)^B / a`; (ii) the optimal threshold allocation
`α_j ∝ w_j^{2/3}` minimises the `2/3`-quasinorm; (iii) the optimised consumer
(`K = 6`) attains the stated weighted cost. The three frozen contracts are
`ThresholdOptimalThresholdAllocation`, `TunableQueryTunableActualQueryComplexity` and
`OptimizedTunableOptimizedTunableConsumer`, with answers `…_answer`. -/
theorem prop6_tunable_query_complexity :
    ThresholdOptimalThresholdAllocation ∧
    TunableQueryTunableActualQueryComplexity ∧
    OptimizedTunableOptimizedTunableConsumer :=
  ⟨ThresholdOptimalThresholdAllocation_answer,
   TunableQueryTunableActualQueryComplexity_answer,
   OptimizedTunableOptimizedTunableConsumer_answer⟩

end Qatlib.Papers.QLSStatePrep24.Amplification
