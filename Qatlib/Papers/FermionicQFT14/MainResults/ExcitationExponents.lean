/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.FermionicQFT14.MainResults.SourceModel

@[expose] public section

/-!
# The two excitation cost branches of Equation (74)

Specializes the scalar cost calculus to the detailed wavepacket-excitation calculation
of Jordan, Lee, and Preskill, arXiv:1404.7115v1, Section 4.3.
-/

set_option autoImplicit false

open Qatlib.Papers.FermionicQFT14.MainResults

namespace Qatlib.Papers.FermionicQFT14.MainResults

/-- The precision and momentum cost models of Equation (74) have respective upper exponents
three and four, allowing independent exponent slack functions in the two limits. -/
theorem excitation_eq74_upper_bounds {cε cp : ℝ} (hcε : 0 ≤ cε) (hcp : 0 ≤ cp)
    {ηε ηp : ℝ → ℝ} (hηε : VanishesAtZero ηε) (hηp : VanishesAtTop ηp) :
    HasUpperBoundAtZero (fun ε => (cε * ε ^ (-(3 : ℝ))) ^ (1 + ηε ε)) 3 ∧
      HasUpperBoundAtTop (fun p => (cp * p ^ (4 : ℝ)) ^ (1 + ηp p)) 4 :=
  ⟨hasUpperBoundAtZero_rpow_one_add_slack hcε hηε,
    hasUpperBoundAtTop_rpow_one_add_slack hcp hηp⟩

end Qatlib.Papers.FermionicQFT14.MainResults
