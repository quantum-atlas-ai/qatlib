/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.WindowLchs.TimeDependentLCHSWindowConsumers
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

variable {I : Type} [Fintype I] [DecidableEq I]

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.LchsSimulation.InhomLeftGrid

noncomputable def inhStep (Mt : ℕ) (s t : ℝ) : ℝ := (t - s) / Mt

noncomputable def inhNode (Mt : ℕ) (s t : ℝ) (l : Fin Mt) : ℝ :=
  s + (l : ℝ) * inhStep Mt s t

noncomputable def inhSourceKUnitary (L H : ℝ → Matrix I I ℂ) (s t : ℝ) (K N Mt : ℕ)
    (j : Fin N) (l : Fin Mt) : Matrix I I ℂ :=
  orderedEvolution (fun u => Complex.I • (H u + staticLchsGrid K N j • L u))
    (inhNode Mt s t l) t

noncomputable def inhSourceSum (L H : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (s t : ℝ)
    (K N Mt : ℕ) : QState I :=
  ∑ l : Fin Mt, (inhStep Mt s t : ℂ) •
    ((∑ j : Fin N, staticLchsCoeff K N j • inhSourceKUnitary L H s t K N Mt j l) *ᵥ
      b (inhNode Mt s t l))

noncomputable def inhSourceResponse (L H : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (s t : ℝ) : QState I :=
  ∫ u in s..t, orderedEvolution (fun y => L y + Complex.I • H y) u t *ᵥ b u
end Qatlib.Concepts.LchsSimulation.InhomLeftGrid
