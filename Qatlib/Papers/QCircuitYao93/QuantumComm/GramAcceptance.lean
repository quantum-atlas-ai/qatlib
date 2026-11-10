/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Foundations.TensorRegisters.GramExpansion
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Papers.QCircuitYao93.QuantumComm.GramAcceptance
open Matrix
open scoped BigOperators
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.TensorRegisters.GramExpansion

theorem lemma3_gram_expansion {E I J : Type}
    [Fintype E] [Fintype I] [Fintype J]
    (a : E → QState I) (b : E → QState J) :
    Inner (∑ e, TensorState (a e) (b e)) (∑ e, TensorState (a e) (b e)) =
      ∑ e, ∑ f, Inner (a e) (a f) * Inner (b e) (b f) := by
  simpa only [Qatlib.Foundations.PureStateMath.Inner, TensorState]
    using! finite_tensor_sum_gram a b

theorem lemma3_acceptance_mass {E I J : Type}
    [Fintype E] [Fintype I] [Fintype J]
    (a : E → QState I) (b : E → QState J) :
    (∑ p, ‖(∑ e, TensorState (a e) (b e)) p‖ ^ 2 : ℝ) =
      (∑ e, ∑ f, Inner (a e) (a f) * Inner (b e) (b f)).re := by
  classical
  have h := congrArg Complex.re (lemma3_gram_expansion a b)
  rw [Qatlib.Foundations.PureStateMath.inner_self] at h
  simpa only [Complex.re_sum, Complex.ofReal_re] using h

end Qatlib.Papers.QCircuitYao93.QuantumComm.GramAcceptance
