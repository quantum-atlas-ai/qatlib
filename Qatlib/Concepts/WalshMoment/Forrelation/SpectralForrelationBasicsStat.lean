/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QmaCompleteness.HistoryHam.SpectralForrelation
set_option warningAsError false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QmaCompleteness.HistoryHam

namespace Qatlib.Concepts.WalshMoment.Forrelation

open Qatlib

def SpectralForrelationBasics : Prop :=
  ∀ (n : ℕ) (S U : Reg n → Bool),
    0 ≤ spectralForrelation n S U ∧
    spectralForrelation n S U ≤ 1 ∧
    (∀ ψ : QState (Reg n), Normalized ψ → forrWitnessMass n S U ψ ≤ spectralForrelation n S U) ∧
    (∀ α : ℝ, α ≤ spectralForrelation n S U →
      ∃ ψ : QState (Reg n), Normalized ψ ∧ α ≤ forrWitnessMass n S U ψ) ∧
    (S = (fun _ => false) → spectralForrelation n S U = 0) ∧
    (U = (fun _ => false) → spectralForrelation n S U = 0)

end Qatlib.Concepts.WalshMoment.Forrelation
