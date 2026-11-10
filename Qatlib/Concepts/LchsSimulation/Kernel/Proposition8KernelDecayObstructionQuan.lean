/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.Kernel.Proposition8KernelDecayObstructionStat
import Qatlib.Concepts.LchsSimulation.Kernel.KernelDecayObstruction
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.LchsSimulation.Kernel

theorem proposition8KernelDecayObstruction : Proposition8KernelDecayObstruction :=
  kernel_decay_obstruction_of_exponential_bound

end Qatlib.Concepts.LchsSimulation.Kernel
