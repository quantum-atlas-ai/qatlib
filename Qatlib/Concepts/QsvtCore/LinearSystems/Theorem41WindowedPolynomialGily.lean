/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.Theorem41WindowedPolynomialStat
import Qatlib.Concepts.QsvtCore.LinearSystems.WindowedReciprocal
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.QsvtCore.LinearSystems

theorem theorem41WindowedPolynomial : Theorem41WindowedPolynomial :=
  Qatlib.Concepts.QsvtCore.LinearSystems.windowed_reciprocal_exists

end Qatlib.Concepts.QsvtCore.LinearSystems
