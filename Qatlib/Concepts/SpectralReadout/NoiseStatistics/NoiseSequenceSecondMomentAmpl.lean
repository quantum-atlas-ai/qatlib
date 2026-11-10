/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralReadout.NoiseStatistics.NoiseSequenceSecondMomentStat
import Qatlib.Concepts.AmpTransform.NoiseMoments.NoiseSequenceMoments
set_option warningAsError false

namespace Qatlib.Concepts.SpectralReadout.NoiseStatistics

theorem noiseSequenceSecondMoment : NoiseSequenceSecondMoment :=
  Qatlib.Concepts.AmpTransform.NoiseMoments.noise_sequence_second_moment

end Qatlib.Concepts.SpectralReadout.NoiseStatistics
