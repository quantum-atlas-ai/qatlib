/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.Lemma2Stat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.HHL2009
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec

set_option autoImplicit false

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter

open Matrix Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec
open scoped Real

def Lemma3 : Prop :=
  ∀ (d θ θ' : ℝ), 0 < d → 0 ≤ θ → θ ≤ 1 / 4 → -1 / 2 ≤ θ' → θ' ≤ 1 / 2 →
    (sinEnvelopeFilterF d θ - sinEnvelopeFilterF d θ') ^ 2 +
        (sinEnvelopeFilterG d θ - sinEnvelopeFilterG d θ') ^ 2 ≤
      2 * Real.pi ^ 2 * (1 / (2 * d)) ^ 2 * (θ - θ') ^ 2 *
        (sinEnvelopeFilterF d θ ^ 2 + sinEnvelopeFilterG d θ ^ 2)

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
