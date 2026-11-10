/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib

noncomputable def sourceCosetDensity (G : Type*) [Group G] [Fintype G]
    (H : Subgroup G) : Matrix G G ℂ := by
  classical
  exact fun p q => if q * p⁻¹ ∈ H then (Fintype.card G : ℂ)⁻¹ else 0

noncomputable def sourceFixedProjector (G : Type*) [Group G] [Fintype G]
    (H : Subgroup G) : Matrix G G ℂ := by
  classical
  exact (Fintype.card H : ℂ)⁻¹ • ∑ h : H, permMatrix (fun g : G => h.val * g)

noncomputable def sourceRightTwirl (G : Type*) [Group G] [Fintype G]
    (rho : Matrix G G ℂ) : Matrix G G ℂ := by
  classical
  exact (Fintype.card G : ℂ)⁻¹ • ∑ g : G,
    let R := permMatrix (fun a : G => a * g)
    R * rho * R.conjTranspose

end Qatlib.Concepts.HspRecovery.ReductionCore
