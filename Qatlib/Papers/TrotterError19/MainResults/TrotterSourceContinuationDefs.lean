/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutator
import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Qatlib.Papers.TrotterError19.MainResults

open Qatlib
open Finset
open scoped BigOperators

def layerTerms {ι : Type} [Fintype ι] (layer : ι → ℕ) (l : ℕ) : Finset ι :=
  Finset.univ.filter (fun i => layer i = l)

noncomputable def layerSiteCount {S ι : Type} [Fintype S] [Fintype ι]
    (supp : ι → Finset S) (layer : ι → ℕ) (l : ℕ) : ℕ :=
  ∑ i, if layer i = l then (supp i).card else 0

end Qatlib.Papers.TrotterError19.MainResults
