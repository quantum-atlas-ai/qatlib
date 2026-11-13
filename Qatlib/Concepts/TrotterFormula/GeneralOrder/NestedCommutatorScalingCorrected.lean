/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.CommutatorTaylorJets

/-!
# Corrected raw commutator bounds for conjugation

This module bounds conjugation by a product of exponentials relative to `pfTaylorBefore`, which
truncates before degree `p`. The bounds use the raw seeded commutator budget without a factorial
divisor and supply corrected estimates for the conjugation remainders considered in the
commutator-scaling framework [ChildsEtAl2021Trotter].

The general estimate includes exponential norm growth, while skew-Hermitian generators yield a
bound with coefficient `pfCommAlphaInner xs B p` and time factor `|t|^p`.

## Main statements

* `pf_conjugation_expansion_general_corrected`: raw-budget remainder bound with exponential
  growth.
* `pf_conjugation_expansion_skew_corrected`: raw-budget remainder bound for skew-Hermitian
  generators.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationWordRemainders
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Bounds conjugation error relative to the Taylor truncation before degree `p` by the raw
inner commutator budget times `|t|^p` and `exp (2 * |t| * suzukiMass xs)`. -/
theorem pf_conjugation_expansion_general_corrected (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p : ℕ) (t : ℝ) :
    ‖suzukiExponentialWord xs t*B*Ring.inverse (suzukiExponentialWord xs t)-
      pfTaylorBefore (fun u=>suzukiExponentialWord xs u*B*Ring.inverse (suzukiExponentialWord xs u)) p t‖≤
      pfCommAlphaInner xs B p*|t| ^p*Real.exp (2*|t| *suzukiMass xs) := by
  let F := fun u=>suzukiExponentialWord xs u*B*Ring.inverse (suzukiExponentialWord xs u)
  have hF : F=pfConjWord xs B := funext (fun u=>(pfConjWord_eq_word_conjugation xs B u).symm)
  change ‖F t-pfTaylorBefore F p t‖≤_
  rw [hF,pfConjWord_taylor_before]
  simpa only [pfWordInflation_false] using! pfConjWord_remainder_norm_mode false xs B p t (by simp)

/-- For skew-Hermitian generators, bounds conjugation error relative to the Taylor truncation
before degree `p` by `pfCommAlphaInner xs B p * |t|^p`. -/
theorem pf_conjugation_expansion_skew_corrected (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p : ℕ) (t : ℝ) (hxs : ∀ X∈xs,Xᴴ=-X) :
    ‖suzukiExponentialWord xs t*B*Ring.inverse (suzukiExponentialWord xs t)-
      pfTaylorBefore (fun u=>suzukiExponentialWord xs u*B*Ring.inverse (suzukiExponentialWord xs u)) p t‖≤
      pfCommAlphaInner xs B p*|t| ^p := by
  let F := fun u=>suzukiExponentialWord xs u*B*Ring.inverse (suzukiExponentialWord xs u)
  have hF : F=pfConjWord xs B := funext (fun u=>(pfConjWord_eq_word_conjugation xs B u).symm)
  change ‖F t-pfTaylorBefore F p t‖≤_
  rw [hF,pfConjWord_taylor_before]
  simpa only [pfWordInflation_true,mul_one] using!
      pfConjWord_remainder_norm_mode true xs B p t (fun _=>hxs)
end Qatlib.Concepts.TrotterFormula.GeneralOrder
