/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.CbDegreeBridge.CbForms
open Qatlib.Concepts.QueryComplexity.CbDegreeBridge

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.NormObstruction

def Lemma3_3FactorizationToAlgorithm : Prop :=
  ∀ (n : ℕ) (t : ℕ) (T : RealTensor (Fin n ⊕ Fin n) (2 * t)),
    HasCbFactorization T → HasSignAlgorithm (tensorBias T) t

end Qatlib.Concepts.QueryComplexity.NormObstruction
