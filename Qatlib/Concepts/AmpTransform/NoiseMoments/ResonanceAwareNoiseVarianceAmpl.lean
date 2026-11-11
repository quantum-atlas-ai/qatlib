/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.NoiseMoments.ResonanceAwareNoiseVarianceStat
import Qatlib.Concepts.AmpTransform.NoiseMoments.NoiseSequenceMoments

/-!
# Resonance-corrected Fourier noise variance

`resonanceAwareNoiseVarianceCorrected` proves the variance formula for an affine Fourier
character sum at every nonzero frequency. The formula includes the additional terms when 2y = 0,
refining the variance expressions associated with Theorems 9 and 10 of [Cornwell2014].

## Main statements

* `resonanceAwareNoiseVarianceCorrected`: Proves the affine noise-intensity variance formula
  with the additional terms at nonzero order-two frequencies, giving the resonance-aware
  correction relevant to [Cornwell, Theorems 9 and 10][Cornwell2014].

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false

namespace Qatlib.Concepts.AmpTransform.NoiseMoments

/-- Proves the affine noise-intensity variance formula with the additional terms at nonzero
order-two frequencies, giving the resonance-aware correction relevant to [Cornwell, Theorems
9 and 10][Cornwell2014]. -/
theorem resonanceAwareNoiseVarianceCorrected : ResonanceAwareNoiseVarianceCorrected :=
  Qatlib.Concepts.AmpTransform.NoiseMoments.noise_sequence_variance_corrected

end Qatlib.Concepts.AmpTransform.NoiseMoments
