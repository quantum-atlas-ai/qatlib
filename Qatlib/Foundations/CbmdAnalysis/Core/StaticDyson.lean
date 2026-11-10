/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.DysonConstruction
import Qatlib.Foundations.CbmdAnalysis.Core.DysonPropagator
import Mathlib.Analysis.SpecialFunctions.Exponential
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
noncomputable section
namespace CBMD
open scoped Matrix.Norms.L2Operator

theorem orderedEvolution_const {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (s t : ℝ) :
    orderedEvolution (fun _ => A) s t = NormedSpace.exp ((t - s) • (-A)) := by
  have he := ordered_matrix_ode_unique (fun _ => A) continuous_const
    (orderedEvolution (fun _ => A) s)
    (fun u : ℝ => NormedSpace.exp ((u - s) • (-A))) s
    (by simp [orderedEvolution_self])
    (orderedEvolution_hasDerivAt _ continuous_const s) (fun u => ?_)
  · exact congrFun he t
  have hd : HasDerivAt (fun v : ℝ => NormedSpace.exp ((v - s) • (-A)))
      ((-A) * NormedSpace.exp ((u - s) • (-A))) u := by
    convert! (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-A) (u - s)).scomp u
      ((hasDerivAt_id u).sub_const s) using 1
    simp
  simpa only [neg_mul] using! hd

theorem dysonPropagator_const_eq_exp {I : Type} [Fintype I] [DecidableEq I]
    (H L : Matrix I I ℂ) (s t : ℝ) (z : ℂ) :
    dysonPropagator (fun _ => H) (fun _ => L) s t z =
      NormedSpace.exp ((-Complex.I * ((t - s : ℝ) : ℂ)) • (H + z • L)) := by
  rw [dysonPropagator, orderedEvolution_const]
  congr 1
  simp only [← neg_smul, ← smul_assoc, Complex.real_smul, mul_comm]

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
