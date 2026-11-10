/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.BlockDefs
set_option warningAsError false

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm

def directionOuter {l m : ℕ} (u : Fin l → ℂ) (v : Fin m → ℂ) :
    Matrix (Fin l) (Fin m) ℂ := fun i j => u i * star (v j)

def directionalBlock (l m : ℕ) (u : Fin l → ℂ) (v : Fin m → ℂ)
    (ell mass tail : ℝ) (z : ℂ) :
    Matrix (Fin l ⊕ Fin m) (Fin l ⊕ Fin m) ℂ :=
  Matrix.fromBlocks
    ((ell : ℂ) • Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.directionOuter u u)
    (z • Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.directionOuter u v)
    (star z • Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.directionOuter v u)
    (((-ell - mass : ℝ) : ℂ) • Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.directionOuter v v +
      (tail : ℂ) • ((1 : Matrix (Fin m) (Fin m) ℂ) - Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.directionOuter v v))
end Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm
