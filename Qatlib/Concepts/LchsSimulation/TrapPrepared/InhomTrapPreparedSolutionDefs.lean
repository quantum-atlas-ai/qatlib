/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.KTrapezoid.InhomogeneousTrapezoidSourceQuadrature
import Qatlib.Concepts.LchsSimulation.WindowLchs.TimeDependentLCHSWindowConsumers
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Unified coefficients for prepared trapezoidal LCHS

`inhTrapUnifiedCoeff` combines homogeneous Cauchy-grid coefficients with source coefficients
weighted by trapezoidal time weights and source norms. `inhTrapUnifiedUnitary` supplies the
corresponding ordered Hamiltonian propagators, using source preparations and inverse input
preparation on source labels.

The mathematical background is described in [AnLiuLin2023].

## Main statements

* `inhTrapUnifiedCoeff`: defines the unified coefficient family.
* `inhTrapUnifiedUnitary`: defines the matching homogeneous and source matrix family.

## References

* [An et al., 2023][AnLiuLin2023]
-/

set_option backward.isDefEq.respectTransparency false
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
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LchsSimulation.KTrapezoid
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.LchsSimulation.TrapPrepared

/-- The coefficient family on `N + N * (Mt + 1)` labels, combining homogeneous Cauchy
coefficients with time-weighted source-norm coefficients. -/
noncomputable def inhTrapUnifiedCoeff (b : ℝ → QState I) (s t : ℝ)
    (K N Mt : ℕ) (x : Fin (N + N * (Mt + 1))) : ℂ :=
  if hx : (x : ℕ) < N then staticLchsCoeff K N ⟨x.val, hx⟩
  else
    let y : Fin (N * (Mt + 1)) := ⟨x.val - N, by have := x.isLt; omega⟩
    let p := finProdFinEquiv.symm y
    (inhTrapWeight Mt s t p.2 : ℂ) * staticLchsCoeff K N p.1 *
      (‖toEuclidean_fromVec (b (inhTrapNode Mt s t p.2))‖ : ℂ)

/-- The matrix family using full-interval ordered Hamiltonian propagation on homogeneous labels
and source-time propagation composed with `P l * Bᴴ` on source labels. -/
noncomputable def inhTrapUnifiedUnitary (L H : ℝ → Matrix I I ℂ) (s t : ℝ)
    (K N Mt : ℕ) (B : Matrix I I ℂ) (P : Fin (Mt + 1) → Matrix I I ℂ)
    (x : Fin (N + N * (Mt + 1))) : Matrix I I ℂ :=
  if hx : (x : ℕ) < N then
    orderedEvolution (fun u => Complex.I • (H u + staticLchsGrid K N ⟨x.val, hx⟩ • L u)) s t
  else
    let y : Fin (N * (Mt + 1)) := ⟨x.val - N, by have := x.isLt; omega⟩
    let p := finProdFinEquiv.symm y
    inhTrapSourceKUnitary L H s t K N Mt p.1 p.2 * (P p.2 * Bᴴ)
end Qatlib.Concepts.LchsSimulation.TrapPrepared
