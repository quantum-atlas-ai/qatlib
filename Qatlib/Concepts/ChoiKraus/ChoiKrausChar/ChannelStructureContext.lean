/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureDefs
public import Qatlib.Concepts.ChannelTheory.Stinespring.PhyslibChannels
public import Qatlib.Concepts.ShadowModels.ShadowChannel.QubitConjugationDesign
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef

@[expose] public section

/-!
# Shared context for Choi–Kraus channel structure

This module is an import prelude for the Choi–Kraus characterization. It assembles the
definitions and supporting imports used by the characterization and applies the local matrix
instance configuration required by its proofs. The declarations themselves live in the imported
channel-structure modules and in `ChoiKrausCorrected`.

## References

* [Choi, 1975][Choi1975]
* [Watrous, 2018][Watrous2018]
-/

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
