/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.HermitianFunctionStability

/-!
# Specification of Gram functional-calculus transfer

This module defines `SvtGramTransfer`, the identity relating the functional calculus of the two
Gram matrices of a rectangular matrix. It packages a spectral transfer used in the
matrix-arithmetic setting of [ChiaEtAl2022].

For every scalar function `g`, sandwiching `g(R*Rᴴ)` between `Rᴴ` and `R` equals applying `x ↦
g(x)*x` to `Rᴴ*R`.

## Main statements

* `SvtGramTransfer`: the adjoint sandwich identity for arbitrary finite rectangular matrices and
  scalar functions.

## References

* [Chia et al., 2022][ChiaEtAl2022]
* [Bhatia, 1997][Bhatia1997]
-/

namespace Qatlib.Concepts.SpectralSketch.SketchSpectral

open Matrix

/-- The proposition that `Rᴴ*g(R*Rᴴ)*R` equals the Hermitian functional calculus of `Rᴴ*R` with
scalar function `x ↦ g(x)*x`, for every finite rectangular matrix and every function `g : ℝ
→ ℂ`. -/
def SvtGramTransfer : Prop :=
  ∀ (K C : Type) [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    (R : Matrix K C ℂ) (g : ℝ → ℂ),
    Rᴴ * Qatlib.Concepts.SpectralSketch.SpectrumPerturb.hermitianFunction (R * Rᴴ)
        (Matrix.isHermitian_mul_conjTranspose_self R) g * R
      = Qatlib.Concepts.SpectralSketch.SpectrumPerturb.hermitianFunction (Rᴴ * R)
        (Matrix.isHermitian_conjTranspose_mul_self R) (fun x => g x * x)

end Qatlib.Concepts.SpectralSketch.SketchSpectral
