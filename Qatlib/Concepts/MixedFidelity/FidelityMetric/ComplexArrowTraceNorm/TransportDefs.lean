/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm.BlockDefs

/-!
# Directional blocks for complex arrow matrices

`directionOuter` forms rectangular rank-one matrices from two vectors. `directionalBlock`
couples two such directions and adds a scalar tail on the complement of the second direction,
providing the matrix representation used in isometric trace-norm transport. See [Bhatia1997].

## Main statements

* `directionOuter`: a rectangular outer product.
* `directionalBlock`: the coupled directional matrix with a scalar tail.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.ComplexArrowTraceNorm

/-- The rectangular outer product with entries `u i * star (v j)`. -/
def directionOuter {l m : ℕ} (u : Fin l → ℂ) (v : Fin m → ℂ) :
    Matrix (Fin l) (Fin m) ℂ := fun i j => u i * star (v j)

/-- The block matrix with diagonal directional terms `ell • u uᴴ` and `(-ell - mass) • v vᴴ +
tail • (1 - v vᴴ)`, coupled by `z • u vᴴ` and its adjoint. -/
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
