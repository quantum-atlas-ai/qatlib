/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureDefs
import Qatlib.Concepts.ChannelTheory.Stinespring.PhyslibChannels
import Qatlib.Concepts.ShadowModels.ShadowChannel.QubitConjugationDesign
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.ChoiKraus.ChoiKrausChar

set_option autoImplicit false

open Matrix
open Qatlib
open scoped Classical ComplexOrder BigOperators

variable {D E : ℕ}

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

end Qatlib.Concepts.ChoiKraus.ChoiKrausChar
