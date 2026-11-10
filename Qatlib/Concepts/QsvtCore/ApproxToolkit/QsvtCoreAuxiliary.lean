/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.QsvtCore
import Qatlib.Concepts.ChoiKraus.ChoiKrausChar.ChannelStructure
import Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
import Qatlib.Concepts.SpectralSketch.SketchSpectral.SvtGramTransferSamp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.LinearAlgebra.Lagrange
import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureKraus
import Qatlib.Concepts.ChannelTheory.Naimark.ChannelStructureMeasurement
import Qatlib.Concepts.ChannelTheory.Naimark.ChannelStructureNaimark
import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureStinespring
import Qatlib.Concepts.ChannelTheory.TwirlChannel
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.QsvtCore.ApproxToolkit

open scoped BigOperators

end Qatlib.Concepts.QsvtCore.ApproxToolkit

namespace Qatlib.Concepts.QsvtCore.ApproxToolkit.S1_QSVT_CORE

open Matrix Polynomial
open scoped Matrix.Norms.L2Operator Classical BigOperators

section Clause11Th20Materials

open Qatlib
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt

end Clause11Th20Materials

section Clause12Cor21Materials

open Module Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open Qatlib.Concepts.SpectralSketch.SketchSpectral
open Qatlib
open Qatlib

end Clause12Cor21Materials

section Clause14RectMaterials

set_option autoImplicit false

noncomputable section

open Polynomial Real

end

set_option autoImplicit false

noncomputable section

open Polynomial Real
open scoped BigOperators

end

set_option autoImplicit false

noncomputable section

open Polynomial Real
open scoped BigOperators

end

set_option autoImplicit false

noncomputable section

open Polynomial Real
open scoped BigOperators
open Qatlib

end

set_option autoImplicit false

noncomputable section

open Polynomial Real
open scoped BigOperators
open Qatlib
end

end Clause14RectMaterials

section Clause13SignMaterials

open Real intervalIntegral MeasureTheory Polynomial

end Clause13SignMaterials

end Qatlib.Concepts.QsvtCore.ApproxToolkit.S1_QSVT_CORE
