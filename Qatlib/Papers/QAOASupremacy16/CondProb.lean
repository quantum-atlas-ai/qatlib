/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.Conditioning
import Qatlib.Papers.QAOASupremacy16.LocalGadget.Native

/-!
# Relative conditioning for the actual gadget output

`actual_gadget_relative_conditioning` applies multiplicative conditioning stability to the
actual local-gadget Born weights. On a selected workspace value with positive reference mass, a
relative approximation error of one tenth bounds each conditional output weight between `9/11`
and `11/9` times its reference value.

This development accompanies the study of QAOA sampling and postselection in [FarhiHarrow2016].

## Main statements

* `actual_gadget_relative_conditioning`: If `p` approximates the selected gadget Born weights
  with relative error at most `1/10` and the selected workspace value has positive reference
  mass, its conditional weight for either Boolean output lies between `9/11` and `11/9` times
  the reference conditional weight.

## References

* [Farhi and Harrow, 2016][FarhiHarrow2016]
-/

set_option warningAsError false
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOASupremacy16.CondProb
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.ProbabilityCore.Conditioning
open Qatlib.Papers.QAOASupremacy16.LocalGadget

/-- If `p` approximates the selected gadget Born weights with relative error at most `1/10` and
the selected workspace value has positive reference mass, its conditional weight for either
Boolean output lies between `9/11` and `11/9` times the reference conditional weight. See
[FarhiHarrow2016]. -/
theorem actual_gadget_relative_conditioning {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : QState (Bool×ι)) (p : Bool×ι→ℝ) (r : ι)
    (hclose : MultiplicativeClose p (fun q=>BornProb (gadgetOutput α) (q.1,(false,q.2))) (1/10))
    (hpos : 0<BornProb (gadgetOutput α) (false,(false,r))+BornProb (gadgetOutput α) (true,(false,r)))
    (b : Bool) :
    (9/11:ℝ)*postSelect (fun q=>BornProb (gadgetOutput α) (q.1,(false,q.2))) r b ≤ postSelect p r b ∧
    postSelect p r b ≤ (11/9:ℝ)*postSelect (fun q=>BornProb (gadgetOutput α) (q.1,(false,q.2))) r b :=
  postSelect_ratio hclose (bornProb_nonneg _ _) (bornProb_nonneg _ _) hpos b
end Qatlib.Papers.QAOASupremacy16.CondProb
