/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.Conditioning
import Qatlib.Papers.QAOASupremacy16.LocalGadget.Native
set_option warningAsError false
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOASupremacy16.CondProb
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.ProbabilityCore.Conditioning
open Qatlib.Papers.QAOASupremacy16.LocalGadget

theorem actual_gadget_relative_conditioning {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : QState (Bool×ι)) (p : Bool×ι→ℝ) (r : ι)
    (hclose : MultiplicativeClose p (fun q=>BornProb (gadgetOutput α) (q.1,(false,q.2))) (1/10))
    (hpos : 0<BornProb (gadgetOutput α) (false,(false,r))+BornProb (gadgetOutput α) (true,(false,r)))
    (b : Bool) :
    (9/11:ℝ)*postSelect (fun q=>BornProb (gadgetOutput α) (q.1,(false,q.2))) r b ≤ postSelect p r b ∧
    postSelect p r b ≤ (11/9:ℝ)*postSelect (fun q=>BornProb (gadgetOutput α) (q.1,(false,q.2))) r b :=
  postSelect_ratio hclose (bornProb_nonneg _ _) (bornProb_nonneg _ _) hpos b
end Qatlib.Papers.QAOASupremacy16.CondProb
