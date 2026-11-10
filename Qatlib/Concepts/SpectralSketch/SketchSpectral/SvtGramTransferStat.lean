/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.HermitianFunctionStability
set_option warningAsError false

namespace Qatlib.Concepts.SpectralSketch.SketchSpectral

open Matrix

def SvtGramTransfer : Prop :=
  ∀ (K C : Type) [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    (R : Matrix K C ℂ) (g : ℝ → ℂ),
    Rᴴ * Qatlib.Concepts.SpectralSketch.SpectrumPerturb.hermitianFunction (R * Rᴴ)
        (Matrix.isHermitian_mul_conjTranspose_self R) g * R
      = Qatlib.Concepts.SpectralSketch.SpectrumPerturb.hermitianFunction (Rᴴ * R)
        (Matrix.isHermitian_conjTranspose_mul_self R) (fun x => g x * x)

end Qatlib.Concepts.SpectralSketch.SketchSpectral
