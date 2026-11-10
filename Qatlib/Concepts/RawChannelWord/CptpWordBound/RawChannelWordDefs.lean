/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SchattenDiamond.DiamondNorm.FiniteDiamondNorm
import Qatlib.Concepts.ReferenceError.DensityToRaw.ChannelTraceContraction
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace

namespace Qatlib.Concepts.RawChannelWord.CptpWordBound
open Matrix
set_option autoImplicit false
noncomputable section

def run {D : ℕ} : List (QuantumChannel D D) → QuantumChannel D D
  | [] => QuantumChannel.id D
  | T::ts => (run ts).comp T

structure ApproxStep (D : ℕ) where
  actual : QuantumChannel D D
  ideal : QuantumChannel D D
  error : ℝ

def actualWord {D : ℕ} (p : List (ApproxStep D)) := run (p.map ApproxStep.actual)
def idealWord {D : ℕ} (p : List (ApproxStep D)) := run (p.map ApproxStep.ideal)
def budget {D : ℕ} (p : List (ApproxStep D)) : ℝ := (p.map ApproxStep.error).sum
end
end Qatlib.Concepts.RawChannelWord.CptpWordBound
