/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

def LearnerCutBridge : Prop := LearnerCutBridgeContract

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
