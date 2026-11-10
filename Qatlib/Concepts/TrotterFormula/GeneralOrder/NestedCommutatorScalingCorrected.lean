/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.CommutatorTaylorJets
set_option warningAsError false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationWordRemainders
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator
variable {I : Type} [Fintype I] [DecidableEq I]

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
