/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

def smallRotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos θ : ℂ), -(Real.sin θ : ℂ); (Real.sin θ : ℂ), (Real.cos θ : ℂ)]

def boundedClip (τ x : ℝ) : ℝ := max (-τ) (min τ x)

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
