/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.WindowLchs.TimeDependentLCHSWindow
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


open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.LchsSimulation.KTrapezoid

noncomputable def kTrapNode (K M : ℕ) (j : Fin (M + 1)) : ℝ :=
  -(K : ℝ) + (j : ℝ) * (2*(K : ℝ)/M)

noncomputable def kTrapWeight (K M : ℕ) (j : Fin (M + 1)) : ℝ :=
  if (j : ℕ) = 0 ∨ (j : ℕ) = M then (K : ℝ)/M else 2*(K : ℝ)/M

noncomputable def kTrapCoeff (K M : ℕ) (j : Fin (M + 1)) : ℂ :=
  ((kTrapWeight K M j/(Real.pi*(1+(kTrapNode K M j)^2))) : ℝ)

noncomputable def kTrapSum (L H : ℝ → Matrix I I ℂ) (s t : ℝ) (K M : ℕ) :
    Matrix I I ℂ :=
  ∑ j : Fin (M+1), kTrapCoeff K M j • orderedEvolution
    (fun u => Complex.I • (H u + (kTrapNode K M j) • L u)) s t
end Qatlib.Concepts.LchsSimulation.KTrapezoid
