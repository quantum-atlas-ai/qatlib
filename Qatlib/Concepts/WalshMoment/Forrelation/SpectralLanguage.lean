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
set_option autoImplicit false

def spectralLangMem (S U : ∀ n, Reg n → Bool) (n : ℕ) : Prop :=
  59 / 100 ≤ spectralForrelation n (S n) (U n)

def spectralPromiseComplete (S U : ∀ n, Reg n → Bool) : Prop :=
  ∀ n : ℕ,
    59 / 100 ≤ spectralForrelation n (S n) (U n) ∨
      spectralForrelation n (S n) (U n) ≤ 57 / 100

end Qatlib.Concepts.WalshMoment.Forrelation
