/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels

/-!
# Learner cut bridge specification

This module defines `LearnerCutBridge` as `LearnerCutBridgeContract` for the Bayesian ordered
search construction of [BenOrHassidim2007]. The proposition combines existence of a balanced
cut, the prefix-mass bounds for the selected cut, and normalization of both answer-conditioned
updates.

## Main definitions

* `LearnerCutBridge`: the cut-selection and posterior-normalization requirements under the
  stated prior and parameter assumptions.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
-/

set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

/-- The proposition `LearnerCutBridgeContract` relating the learner's selected balanced cut to
nonemptiness of the cut set and normalization of the two posterior updates. -/
def LearnerCutBridge : Prop := LearnerCutBridgeContract

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
