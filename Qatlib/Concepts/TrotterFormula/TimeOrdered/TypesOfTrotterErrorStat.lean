/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.TimeOrdered.TrotterErrorTypes
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationWordRemainders
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.TrotterFormula.TimeOrdered

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator

def TypesOfTrotterError : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (xs : List (Matrix I I ℂ))
    (H : Matrix I I ℂ) (t : ℝ),

    (suzukiExponentialWord xs t - NormedSpace.exp (t • H) =
      ∫ τ in 0..t,
        NormedSpace.exp ((t - τ) • H) *
          (suzukiExponentialWord xs τ * pfWordDefectRight xs H τ)) ∧

    (∀ τ : ℝ,
      pfWordDefectRight xs H τ =
        (∑ j : Fin xs.length,
            Ring.inverse (suzukiExponentialWord (xs.drop (j.val + 1)) τ) *
              xs.getD j.val 0 *
              suzukiExponentialWord (xs.drop (j.val + 1)) τ) -
          Ring.inverse (suzukiExponentialWord xs τ) * H *
            suzukiExponentialWord xs τ) ∧

    (suzukiExponentialWord xs t =
      orderedEvolution (fun τ => -(H + pfWordDefectLeft xs H τ)) 0 t) ∧

    (∀ τ : ℝ,
      pfWordDefectLeft xs H τ =
        (∑ j : Fin xs.length,
            pfConjWord (xs.take j.val) (xs.getD j.val 0) τ) - H) ∧

    (suzukiExponentialWord xs t =
      NormedSpace.exp (t • H) *
        orderedEvolution (fun τ => -(pfWordMultiplicativeField xs H τ)) 0 t)

end Qatlib.Concepts.TrotterFormula.TimeOrdered
