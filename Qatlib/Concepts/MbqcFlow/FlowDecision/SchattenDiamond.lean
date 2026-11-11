/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.RectangularSchattenHolder
import Qatlib.Concepts.MbqcFlow.FlowDecision.SchattenDiamondDefs

/-!
# Schatten inequality import interface

Provides an import interface for the rectangular Schatten results in `RectangularSchattenHolder`
and the base imports in `SchattenDiamondDefs`. In particular, the imported theorem
`rectangular_holder` supplies the rectangular Hölder bound for `schattenPower`.

This module adds no declarations of its own. The matrix-analysis background for the imported
inequalities is given in [Bhatia1997].

## Main statements

* `RectangularSchattenHolder.rectangular_holder`: imported rectangular Schatten Hölder
  inequality.

## References

* [Bhatia, 1997][Bhatia1997]
-/

open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
