module

import Qatlib.Papers.ContDiscWalk08.CompressedSim.OperatorNormBridge

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open scoped Matrix.Norms.L2Operator

namespace QatlibTests.ContDiscWalk08OperatorNorm

open Qatlib.Papers.ContDiscWalk08.CompressedSim

/- A concrete two-level model exercises the public operator-norm theorem. -/
example :
    ‖Matrix.diagonal (fun i : Fin 2 => phaseError (if i = 0 then (0 : ℝ) else 1 / 2) 1)‖
      ≤ 3 := by
  have hLam : ∀ i : Fin 2, |(if i = 0 then (0 : ℝ) else 1 / 2)| ≤ 1 := by
    intro i
    fin_cases i <;> norm_num
  have h := diagonal_phaseError_norm_le_uniform
    (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1 / 2) 1 hLam
  norm_num at h ⊢
  exact h

end QatlibTests.ContDiscWalk08OperatorNorm
