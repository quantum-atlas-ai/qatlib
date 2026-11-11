/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Defs

/-!
# Shared context for CNOT measurement patterns

This module imports the shared CNOT-pattern definitions and supplies the namespace and scope
context used by the clause and gadget proofs. The imported vocabulary includes `MpPattern` and
`mpPatternKraus`, representing finite measurement patterns and their branch operators in the
setting of [DanosKashefiPanangaden2007].

## Main statements

* `MpPattern`: Imported finite measurement-pattern data used by the CNOT development.
* `mpPatternKraus`: Imported Kraus matrices used to express branch semantics.

## References

* [Danos et al., 2007][DanosKashefiPanangaden2007]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

open Qatlib.Concepts.ClusterPatterns.CnotPatterns
open scoped BigOperators Classical

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.ClusterPatterns.CnotPatterns

end Qatlib.Concepts.ClusterPatterns.CnotPatterns

namespace Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra

open Qatlib.Concepts.ClusterPatterns.CnotPatterns

end Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra

namespace Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra

open Qatlib.Concepts.ClusterPatterns.CnotPatterns

end Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra

namespace Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra

open Qatlib.Concepts.ClusterPatterns.CnotPatterns

end Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra

namespace Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire

open Qatlib.Concepts.ClusterPatterns.CnotPatterns

end Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire

namespace Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire1a

open Qatlib.Concepts.ClusterPatterns.CnotPatterns
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire

end Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire1a

namespace Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic

end Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic

namespace Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic

open Qatlib.Concepts.ClusterPatterns.CnotPatterns
open scoped BigOperators Classical

namespace Clause18Euler2

open Qatlib.Concepts.ClusterPatterns.CnotPatterns
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra

end Clause18Euler2

namespace Clause18Euler2

open Qatlib.Concepts.ClusterPatterns.CnotPatterns
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra

end Clause18Euler2

open Qatlib.Concepts.ClusterPatterns.CnotPatterns
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra

set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000
open Qatlib.Concepts.ClusterPatterns.CnotPatterns
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire1a
open scoped BigOperators Classical

end Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
