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
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification
noncomputable def goodProjection {ι H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ι ℂ H) (label : ι → ℤ) (χ : ℤ → Bool) :
    H →L[ℂ] H :=
  ((Submodule.span ℂ
    ((fun i : ι => b i) '' {i : ι | χ (label i) = true})).topologicalClosure).starProjection
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
noncomputable def run {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H ≃ₗᵢ[ℂ] H) (e : H) (P : H →L[ℂ] H)
    (r : ℝ) (program : List (Fin 6)) : H × H :=
  program.foldl (fun v k => step A e P r k v) (e, 0)
def calls (program : List (Fin 6)) : ℕ :=
  (program.filter (fun k => decide (k.val < 2))).length
end Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification
