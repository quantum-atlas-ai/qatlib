/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels

/-!
# Generalized Markov estimate specification

This module defines `GeneralizedMarkov` as the proposition `GeneralizedMarkovContract`. It
specifies a tail estimate for a nonnegative random variable from an upper bound on its mean and
a lower bound on the probability of exceeding a lower threshold, as used in [BenOrHassidim2007].

## Main definitions

* `GeneralizedMarkov`: the bound P(X > c) ≤ (a - b + βb) / (c - b) under the contract's
  hypotheses.

## References

* [Ben-Or and Hassidim, Lemma 2.8][BenOrHassidim2007]
-/

set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

/-- The generalized Markov proposition `GeneralizedMarkovContract`, bounding P(X > c) using the
mean of X and a lower bound on P(X ≥ b). -/
def GeneralizedMarkov : Prop := GeneralizedMarkovContract

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
