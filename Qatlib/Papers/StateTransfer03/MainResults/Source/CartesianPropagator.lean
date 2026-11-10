/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StateTransfer03.MainResults.Defs
set_option warningAsError false

namespace Qatlib.Papers.StateTransfer03.MainResults.Source

open scoped BigOperators
open Qatlib.Papers.StateTransfer03.MainResults.Defs

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

noncomputable section

theorem cartesian_eigenvalue_additive {ι κ : Type*} (E : ι → ℝ) (F : κ → ℝ)
    (p : ι × κ) :
    productEigenvalue E F p = E p.1 + F p.2 :=
  rfl

theorem cartesian_product_amplitude {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : ι → ℝ) (u : ι → ℂ) (F : κ → ℝ) (v : κ → ℂ) (t : ℝ) :
    spectralAmplitude (productEigenvalue E F) (productWeight u v) t =
      spectralAmplitude E u t * spectralAmplitude F v t :=
  spectralAmplitude_prod E u F v t

theorem cartesian_power_amplitude {ι : Type*} [Fintype ι]
    (E : ι → ℝ) (u : ι → ℂ) (d : ℕ) (t : ℝ) :
    spectralAmplitude (powerEigenvalue E d) (powerWeight u d) t =
      spectralAmplitude E u t ^ d :=
  spectralAmplitude_pow E u d t

theorem path_power_amplitude (N d : ℕ) (t : ℝ) :
    spectralAmplitude (powerEigenvalue (pathEigenvalue N) d)
        (powerWeight (fun k => (pathWeight N k : ℂ)) d) t =
      pathSpectralAmplitude N t ^ d :=
  spectralAmplitude_pow (pathEigenvalue N)
    (fun k => (pathWeight N k : ℂ)) d t

theorem path_power_unit_modulus (N d : ℕ) (t : ℝ)
    (h : ‖pathSpectralAmplitude N t‖ = 1) :
    ‖spectralAmplitude (powerEigenvalue (pathEigenvalue N) d)
        (powerWeight (fun k => (pathWeight N k : ℂ)) d) t‖ = 1 := by
  rw [path_power_amplitude, norm_pow, h, one_pow]

end

end Qatlib.Papers.StateTransfer03.MainResults.Source
