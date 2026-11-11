/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Foundations.PureStateMath.MixedState

/-!
# Projector code operators for information hiding

`lemma8CodeState` forms a linear combination of the identity and a supplied operator, with
coefficients parameterized by dimension, rank, and signal strength. This is the code-operator
formula used in the finite POVM information-hiding argument; positivity and trace conditions are
handled separately.

These constructions support the treatment in [HuangKuengPreskill2020].

## Main statements

* `lemma8CodeState`: defines `(1 - α) I / d + α P / r`.

## References

* [Huang et al., 2020][HuangKuengPreskill2020]
-/

open Qatlib.Foundations.PureStateMath

open Matrix
open scoped ComplexOrder
open scoped Classical BigOperators

namespace Qatlib.Papers.ClassShadows20.LowerBound

/-- The code operator `((1 - α) / d) • I + (α / r) • P`, without assumptions on the input
operator or parameters. -/
noncomputable def lemma8CodeState (d r : ℕ) (α : ℝ) (P : Operator d) :
    Operator d :=
  ((1 - α) / (d : ℝ)) • 1 + (α / (r : ℝ)) • P
end Qatlib.Papers.ClassShadows20.LowerBound
