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
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.IntWordFraming.WordFraming
open Qatlib.Concepts.WalshMoment.Forrelation

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open Qatlib
open scoped Classical BigOperators

def algExpBitCost (N e : ℕ) : ℕ := e * N

def algLocalQFTGateCost (n : ℕ) : ℕ := n + n * (n - 1) / 2 + n / 2

def algDecompositionPayload {m n : ℕ} (p : NormalizedSmithData m n) : ℕ × ℕ :=
  ((p.binaryFactors.map List.length).sum,
    (p.binaryGeneratorWords.map (fun w => ∑ i : Fin m, (1 + w[i.val].2.length))).sum)

def algDecompositionPayloadTotal {m n : ℕ} (p : NormalizedSmithData m n) : ℕ :=
  (algDecompositionPayload p).1 + (algDecompositionPayload p).2

end Qatlib.Concepts.HspRecovery.ReductionCore
