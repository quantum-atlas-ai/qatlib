/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Foundations.TensorRegisters.GramExpansion

/-!
# Gram expansions of tensor acceptance mass

The module expands the squared norm of a finite sum of tensor product states as a double sum of
products of Gram matrix entries. Taking real parts gives the corresponding total
squared-amplitude formula used in communication protocol estimates. See [Yao1993].

## Main statements

* `lemma3_gram_expansion`: expands the inner product of the tensor sum.
* `lemma3_acceptance_mass`: expresses total squared amplitude by the real Gram sum.

## References

* [Yao, 1993][Yao1993]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Papers.QCircuitYao93.QuantumComm.GramAcceptance
open Matrix
open scoped BigOperators
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.TensorRegisters.GramExpansion

/-- The squared norm, expressed as an inner product, of `∑ e, TensorState (a e) (b e)` equals
the double sum of products of the two families' Gram entries. -/
theorem lemma3_gram_expansion {E I J : Type}
    [Fintype E] [Fintype I] [Fintype J]
    (a : E → QState I) (b : E → QState J) :
    Inner (∑ e, TensorState (a e) (b e)) (∑ e, TensorState (a e) (b e)) =
      ∑ e, ∑ f, Inner (a e) (a f) * Inner (b e) (b f) := by
  simpa only [Qatlib.Foundations.PureStateMath.Inner, TensorState]
    using! finite_tensor_sum_gram a b

/-- The total squared amplitude of the tensor sum equals the real part of the double sum of
products of Gram entries. This is the acceptance-mass identity associated with Lemma 3 and
the proof of Theorem 4 in [Yao1993]. -/
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
