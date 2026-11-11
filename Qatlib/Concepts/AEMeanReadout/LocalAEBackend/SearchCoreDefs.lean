/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle

/-!
# Rotation and clipping primitives

This module defines `smallRotation`, the real plane rotation viewed as a complex two-dimensional
matrix, and `boundedClip`, the scalar expression max (−τ) (min τ x). For nonnegative τ, the
latter clips a real value to the interval [−τ, τ]. These primitives support local circuit and
numerical readout constructions in the quantum-computation setting of [NielsenChuang2010].

## Main definitions

* `smallRotation`: a two-dimensional rotation matrix with cosine and sine entries.
* `boundedClip`: symmetric scalar clipping for a nonnegative threshold.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

/-- The complex two-dimensional matrix with rows (cos θ, −sin θ) and (sin θ, cos θ). -/
def smallRotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos θ : ℂ), -(Real.sin θ : ℂ); (Real.sin θ : ℂ), (Real.cos θ : ℂ)]

/-- The scalar expression max (−τ) (min τ x), which clips x to [−τ, τ] when τ is nonnegative. -/
def boundedClip (τ x : ℝ) : ℝ := max (-τ) (min τ x)

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
