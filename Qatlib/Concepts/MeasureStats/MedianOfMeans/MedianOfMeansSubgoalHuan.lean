/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MeasureStats.MedianOfMeans.MedianOfMeansSubgoalStat

namespace Qatlib.Concepts.MeasureStats.MedianOfMeans

open Qatlib

theorem medianOfMeansSubgoal : MedianOfMeansSubgoal := fun
  X _ _ p f L M hL hM ε δ hε hδ hvar hMδ =>
    (Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.median_of_means_concentration p f hL hM ε hε hvar).trans hMδ

end Qatlib.Concepts.MeasureStats.MedianOfMeans
