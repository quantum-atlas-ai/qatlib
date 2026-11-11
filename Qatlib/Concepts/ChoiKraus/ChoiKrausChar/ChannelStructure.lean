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

/-!
# Shared context for Choi–Kraus channel structure

This module assembles the definitions and supporting imports used by the Choi–Kraus
characterization. In particular, `ChoiMatrix`, `KrausForm`, and `KrausComplete` express the
finite matrix conventions underlying the characterization of completely positive maps
[Choi1975].

The imported Physlib channel conversions and qubit conjugation-design results provide a common
context for subsequent channel structure proofs.

## Main definitions

* `ChoiMatrix`: the matrix of a linear map evaluated on matrix units.
* `KrausForm` and `KrausComplete`: operator-sum representation and completeness.
* `channelEquivPhyslib`: the equivalence with Physlib's bundled CPTP maps.

## References

* [Choi, 1975][Choi1975]
* [Watrous, 2018][Watrous2018]
-/

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
