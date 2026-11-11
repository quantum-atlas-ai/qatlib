/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.Kernel.Proposition8KernelDecayObstructionStat
import Qatlib.Concepts.LchsSimulation.Kernel.KernelDecayObstruction

/-!
# Exponential kernel decay obstruction

`proposition8KernelDecayObstruction` establishes the vanishing conclusion for bounded analytic
lower-half-plane kernels with exponential boundary decay. This is the obstruction associated
with Proposition 8 in the near-optimal LCHS analysis. See [AnChildsLin2026] for the mathematical
setting.

## Main statements

* `proposition8KernelDecayObstruction`: A bounded function analytic in the open lower half-plane
  and continuous on its closure must vanish there if its real-axis values decay exponentially,
  as formalized for [An, Childs, and Lin, Proposition 8][AnChildsLin2026].

## References

* [An, Childs, and Lin, 2026][AnChildsLin2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.LchsSimulation.Kernel

/-- A bounded function analytic in the open lower half-plane and continuous on its closure must
vanish there if its real-axis values decay exponentially, as formalized for [An, Childs, and
Lin, Proposition 8][AnChildsLin2026]. -/
theorem proposition8KernelDecayObstruction : Proposition8KernelDecayObstruction :=
  kernel_decay_obstruction_of_exponential_bound

end Qatlib.Concepts.LchsSimulation.Kernel
