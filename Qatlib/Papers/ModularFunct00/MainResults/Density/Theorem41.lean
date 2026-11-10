/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ModularFunct00.MainResults.Setup
import Qatlib.Papers.ModularFunct00.MainResults.Examples
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ModularFunct00.MainResults.Density

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Papers.ModularFunct00.MainResults.Examples

def ImageClosure {G : Type*} [Group G] (ρ5 : G → CM 5) (ρ8 : G → CM 8) :
    Set (CM 5 × CM 8) :=
  closure (Set.range (fun b : G => (ρ5 b, ρ8 b)))

theorem theorem4_1_image_subset_closure {G : Type*} [Group G]
    (ρ5 : G → CM 5) (ρ8 : G → CM 8) :
    Set.range (fun b : G => (ρ5 b, ρ8 b)) ⊆ ImageClosure ρ5 ρ8 :=
  subset_closure

theorem theorem4_1_isClosed {G : Type*} [Group G]
    (ρ5 : G → CM 5) (ρ8 : G → CM 8) :
    IsClosed (ImageClosure ρ5 ρ8) :=
  isClosed_closure

theorem theorem4_1_eigenvalue_ratio_not_pm_one {q : ℂ} (hq5 : q ^ 5 = 1)
    (hq1 : q ≠ 1) :
    q / (-1) ≠ 1 ∧ q / (-1) ≠ -1 :=
  fiveRoot_ratio_ne_pm_one hq5 hq1

theorem theorem4_1_negation_twist_forces_one {q : ℂ}
    (h : ∀ μ ∈ ({(-1 : ℂ), q} : Set ℂ), -μ ∈ ({(-1 : ℂ), q} : Set ℂ)) :
    q = 1 :=
  negation_closed_two_element_forces_one h

theorem theorem4_1_no_fifth_root_multiplicative_closure {q : ℂ} (ω : ℂ)
    (hω5 : ω ^ 5 = 1) (hω1 : ω ≠ 1) :
    ¬ ∀ μ ∈ ({(-1 : ℂ), q} : Set ℂ), ω * μ ∈ ({(-1 : ℂ), q} : Set ℂ) :=
  not_mul_closed_two_element_fifth_root ω hω5 hω1

end Qatlib.Papers.ModularFunct00.MainResults.Density
