/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsTransportDefs

/-!
# Resource-bound transport interface

This module imports the resource-bound transport definitions into the adversary-bound
development. Through `ResourceBoundsTransportDefs`, it exposes the account and ledger interfaces
used to compare query, gate, classical-bit, and space costs. For background on these
computational resources, see [NielsenChuang2010].

## Main statements

* `Account`: The imported account interface for work and peak-space resources.
* `FreshLedger`: The imported ledger interface for fresh-copy computations.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.FreshCopyExec.QpeConsumers

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.ResourceBounds.AsymBounds
open Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Qatlib
open Qatlib
open scoped ENNReal

noncomputable section

end
end Qatlib.Concepts.AdversaryBounds.AdvDuality
