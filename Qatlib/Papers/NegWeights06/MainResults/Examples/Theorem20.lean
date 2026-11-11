/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryFourBitWitness

set_option backward.isDefEq.respectTransparency false

/-!
# NegWeights06, Theorem 20 — the four-bit Ambainis function

Source: Høyer–Lee–Špalek, "Negative weights make adversaries stronger",
arXiv:quant-ph/0611054v2 (fixed PDF, SHA256
`8c705081dc3243baa1c83a64ed92870c7cd42fa91dd872c469621158af2c37bb`),
Theorem 20, §7.1, printed page 24:

`ADV±(f) ≥ 2.5135` for Ambainis' four-bit sorted function `f : {0,1}^4 → {0,1}`.

The paper-layer theorem is a reference/bridge to the frozen explicit witness
`QuantumAlgorithm.Concepts.AdversaryBounds.AdvDuality.ambainis_four_bit_printed_bound`,
which constructs the printed rational negative-weight adversary matrix and
proves `2.5135 = 25135/10000 ≤ advPmValue (fun w => w) ambainisSorted4`.
The frozen witness has every filter norm at most one and row sum `2513526/1000005`,
exactly the printed certificate.
-/

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Papers.NegWeights06.MainResults.Examples

open Qatlib
open Qatlib.Concepts.AdversaryBounds.AdvDuality

noncomputable section

/-- **Theorem 20 (Ambainis' four-bit function).**
`ADV±(f) ≥ 2.5135` for the four-bit sorted function `ambainisSorted4`.

The paper's `f : {0,1}^4 → {0,1}` is `ambainisSorted4`, and `ADV±` is the frozen
`advPmValue` (supremum over complex Hermitian same-output-zero witnesses). -/
theorem theorem20_four_bit_bound :
    ENNReal.ofReal (2.5135 : ℝ) ≤
      advPmValue (fun w : FourBitWord => w) ambainisSorted4 := by
  have hdec : (2.5135 : ℝ) = 25135 / 10000 := by norm_num
  rw [hdec]
  exact ambainis_four_bit_printed_bound

end

end Qatlib.Papers.NegWeights06.MainResults.Examples
