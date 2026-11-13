/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StateTransfer03.MainResults.Defs

/-!
# Cartesian product identities for spectral propagators

This module specializes the spectral product rules to Cartesian products and powers, including
the path spectral data. It proves that unit-modulus path amplitudes remain of unit modulus under
every finite spectral power, expressing the Cartesian transfer mechanism of
[ChristandlEtAl2004].

## Main statements

* `cartesian_product_amplitude`: product spectral data give the product of amplitudes.
* `cartesian_power_amplitude`: spectral powers give scalar powers of the amplitude.
* `path_power_unit_modulus`: a unit-modulus path amplitude remains unit-modulus in every
  spectral power.

## References

* [Christandl et al., 2004][ChristandlEtAl2004]
-/

namespace Qatlib.Papers.StateTransfer03.MainResults.Source

open scoped BigOperators
open Qatlib.Papers.StateTransfer03.MainResults.Defs

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

/-- The energy assigned to a Cartesian product index is the sum of its two component energies. -/
theorem cartesian_eigenvalue_additive {ι κ : Type*} (E : ι → ℝ) (F : κ → ℝ)
    (p : ι × κ) :
    productEigenvalue E F p = E p.1 + F p.2 :=
  rfl

/-- The spectral amplitude for Cartesian product data is the product of the two component
amplitudes. -/
theorem cartesian_product_amplitude {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : ι → ℝ) (u : ι → ℂ) (F : κ → ℝ) (v : κ → ℂ) (t : ℝ) :
    spectralAmplitude (productEigenvalue E F) (productWeight u v) t =
      spectralAmplitude E u t * spectralAmplitude F v t :=
  spectralAmplitude_prod E u F v t

/-- The amplitude of the `d`-fold spectral Cartesian power is the `d`th power of the original
amplitude [ChristandlEtAl2004]. -/
theorem cartesian_power_amplitude {ι : Type*} [Fintype ι]
    (E : ι → ℝ) (u : ι → ℂ) (d : ℕ) (t : ℝ) :
    spectralAmplitude (powerEigenvalue E d) (powerWeight u d) t =
      spectralAmplitude E u t ^ d :=
  spectralAmplitude_pow E u d t

/-- The amplitude of the `d`-fold path spectral power is `pathSpectralAmplitude N t ^ d`
[ChristandlEtAl2004]. -/
theorem path_power_amplitude (N d : ℕ) (t : ℝ) :
    spectralAmplitude (powerEigenvalue (pathEigenvalue N) d)
        (powerWeight (fun k => (pathWeight N k : ℂ)) d) t =
      pathSpectralAmplitude N t ^ d :=
  spectralAmplitude_pow (pathEigenvalue N)
    (fun k => (pathWeight N k : ℂ)) d t

/-- If the path spectral amplitude has norm one at time `t`, the amplitude of every finite
spectral power also has norm one at that time. -/
theorem path_power_unit_modulus (N d : ℕ) (t : ℝ)
    (h : ‖pathSpectralAmplitude N t‖ = 1) :
    ‖spectralAmplitude (powerEigenvalue (pathEigenvalue N) d)
        (powerWeight (fun k => (pathWeight N k : ℂ)) d) t‖ = 1 := by
  rw [path_power_amplitude, norm_pow, h, one_pow]

end

end Qatlib.Papers.StateTransfer03.MainResults.Source
