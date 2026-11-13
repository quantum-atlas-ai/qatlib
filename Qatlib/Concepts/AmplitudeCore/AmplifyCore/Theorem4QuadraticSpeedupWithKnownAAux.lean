/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Span.Defs
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem2QuadraticSpeedupRestrictedQuan
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Execution model for exact amplitude amplification

`step` interprets six instructions acting on a pair of Hilbert space vectors, including
preparation, its inverse, ancillary rotations, and reflections. `run` executes a program from
the initial pair, and `calls` counts preparation and inverse preparation instructions. See
[BrassardEtAl2002] for background.

## Main statements

* `step`: Interprets one of six exact amplification instructions on a vector pair, using the
  ancillary mixing parameter `r`.
* `run`: Executes the instruction list from `(e, 0)` by applying `step` in list order.
* `calls`: The number of preparation or inverse preparation instructions in a program.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification
/-- The orthogonal projection onto the closed span of basis vectors whose integer labels are
marked by `χ`. -/
noncomputable def goodProjection {ι H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ι ℂ H) (label : ι → ℤ) (χ : ℤ → Bool) :
    H →L[ℂ] H :=
  ((Submodule.span ℂ
    ((fun i : ι => b i) '' {i : ι | χ (label i) = true})).topologicalClosure).starProjection
/-- Interprets one of six exact amplification instructions on a vector pair, using the ancillary
mixing parameter `r`. -/
noncomputable def step {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H ≃ₗᵢ[ℂ] H) (e : H) (P : H →L[ℂ] H)
    (r : ℝ) (k : Fin 6) (v : H × H) : H × H :=
  let c : ℂ := (Real.sqrt (1 - r) : ℂ);
  let s : ℂ := (Real.sqrt r : ℂ);
  match k.val with
  | 0 => (A v.1, A v.2)
  | 1 => (A.symm v.1, A.symm v.2)
  | 2 => (c • v.1 - s • v.2, s • v.1 + c • v.2)
  | 3 => (c • v.1 + s • v.2, -s • v.1 + c • v.2)
  | 4 => (-v.1 + ((2 : ℂ) * inner ℂ e v.1) • e, -v.2)
  | _ => (v.1, v.2 - (2 : ℂ) • P v.2)
/-- Executes the instruction list from `(e, 0)` by applying `step` in list order. -/
noncomputable def run {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H ≃ₗᵢ[ℂ] H) (e : H) (P : H →L[ℂ] H)
    (r : ℝ) (program : List (Fin 6)) : H × H :=
  program.foldl (fun v k => step A e P r k v) (e, 0)
/-- The number of preparation or inverse preparation instructions in a program. -/
def calls (program : List (Fin 6)) : ℕ :=
  (program.filter (fun k => decide (k.val < 2))).length
end Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification
