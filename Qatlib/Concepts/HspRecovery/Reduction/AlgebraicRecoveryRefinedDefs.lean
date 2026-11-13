/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.CompactPresentationRecovery
import Qatlib.Concepts.WalkFind.UniformThree.FourierRecovery
import Qatlib.Concepts.PeriodSampling.OrderRecovery.RandomBaseFactor
import Qatlib.Concepts.HspRecovery.CfOrder.CompositeOrderDlogDecoder
import Qatlib.Concepts.QftPreparation.LocalQft

/-!
# Refined algebraic recovery cost expressions

This module defines numerical cost expressions for exponentiation and a local quantum Fourier
transform. It also counts the binary factor and generator-word payload carried by
`NormalizedSmithData`, separately and in total. See [NielsenChuang2010] for the mathematical
background.

## Main statements

* `algLocalQFTGateCost`: the local Fourier gate-count expression.
* `algDecompositionPayload`: factor and generator-word payload sizes.
* `algDecompositionPayloadTotal`: their sum.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.IntWordFraming.WordFraming
open Qatlib.Concepts.WalshMoment.Forrelation

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open Qatlib
open scoped Classical BigOperators

/-- The exponentiation bit-cost expression `e * N`. -/
def algExpBitCost (N e : ℕ) : ℕ := e * N

/-- The local Fourier gate-cost expression `n + n * (n - 1) / 2 + n / 2`. -/
def algLocalQFTGateCost (n : ℕ) : ℕ := n + n * (n - 1) / 2 + n / 2

/-- The pair consisting of total binary factor length and total signed generator-word payload
length. -/
def algDecompositionPayload {m n : ℕ} (p : NormalizedSmithData m n) : ℕ × ℕ :=
  ((p.binaryFactors.map List.length).sum,
    (p.binaryGeneratorWords.map (fun w => ∑ i : Fin m, (1 + w[i.val].2.length))).sum)

/-- The sum of the factor and generator-word payload counts in `algDecompositionPayload`. -/
def algDecompositionPayloadTotal {m n : ℕ} (p : NormalizedSmithData m n) : ℕ :=
  (algDecompositionPayload p).1 + (algDecompositionPayload p).2

end Qatlib.Concepts.HspRecovery.ReductionCore
