/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralReadout.NoiseStatistics.NoiseSequenceSecondMomentStat
import Qatlib.Concepts.AmpTransform.NoiseMoments.NoiseSequenceMoments

/-!
# Noise-sequence second moments

This module supplies `noiseSequenceSecondMoment`, proving the finite uniform character-sum
moment specification `NoiseSequenceSecondMoment`. It transfers the underlying noise-moment
result to the spectral-readout interface used for the intensity calculations of [Cornwell2014].

## Main statements

* `noiseSequenceSecondMoment`: the unshifted second moment and the shifted real-scaled second
  moment.

## References

* [Cornwell, 2014, Theorems 4 and 5][Cornwell2014]
-/

namespace Qatlib.Concepts.SpectralReadout.NoiseStatistics

/-- Establish the uniform noise-sequence second-moment specification, including the shifted
real-scaled character-sum identity. See [Cornwell2014]. -/
theorem noiseSequenceSecondMoment : NoiseSequenceSecondMoment :=
  Qatlib.Concepts.AmpTransform.NoiseMoments.noise_sequence_second_moment

end Qatlib.Concepts.SpectralReadout.NoiseStatistics
