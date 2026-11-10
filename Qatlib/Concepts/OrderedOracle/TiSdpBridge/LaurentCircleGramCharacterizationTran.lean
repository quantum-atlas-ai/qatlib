/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentCircleGramCharacterizationStat
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentCircleSpectralFactorTran
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Qatlib.Concepts.OrderedOracle.TiSdpBridge Polynomial Matrix
open scoped Classical BigOperators ComplexOrder

theorem laurentCircleGramCharacterization : LaurentCircleGramCharacterization := by
  intro n a
  constructor
  · intro ha
    obtain ⟨p,_,_,hcoeff,hps,_,_⟩ := laurentCircleSpectralFactor n a ha
    refine ⟨gramOuter p,hps,hcoeff,?_,?_⟩
    · intro z
      exact (complexLaurentEval_eq_matrixLaurent_of_genTrace a (gramOuter p) hcoeff z).symm
    · simpa only [genTrace_zero] using hcoeff 0
  · rintro ⟨A,hps,hcoeff,_,_⟩
    exact complexLaurentNonnegative_of_gram_posSemidef a A hps hcoeff

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
