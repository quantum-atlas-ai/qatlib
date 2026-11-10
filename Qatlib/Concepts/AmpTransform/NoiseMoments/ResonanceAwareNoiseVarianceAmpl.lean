/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.NoiseMoments.ResonanceAwareNoiseVarianceStat
import Qatlib.Concepts.AmpTransform.NoiseMoments.NoiseSequenceMoments
set_option warningAsError false

namespace Qatlib.Concepts.AmpTransform.NoiseMoments

theorem resonanceAwareNoiseVarianceCorrected : ResonanceAwareNoiseVarianceCorrected :=
  Qatlib.Concepts.AmpTransform.NoiseMoments.noise_sequence_variance_corrected

end Qatlib.Concepts.AmpTransform.NoiseMoments
