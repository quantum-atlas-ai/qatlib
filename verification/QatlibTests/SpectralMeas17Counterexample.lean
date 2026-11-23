module

import Qatlib.Papers.SpectralMeas17.PauliExpect.Counterexample

@[expose] public section

/-! Ordinary-module consumer for the Equation (8) identifiability boundary. -/

set_option autoImplicit false

namespace Tests.SpectralMeas17Counterexample

open Qatlib.Papers.SpectralMeas17.PauliExpect

example : eq8Factor 0 (-1) = 0 := by
  exact eq8Factor_zero_response

example :
    eq8Observation 0 (-1) 1 0 ∧ (1 : ℝ) ≠ 0 / eq8Factor 0 (-1) := by
  exact eq8_zero_response_witness

example :
    ¬ (∀ E Gamma target walk : ℝ, eq8Observation E Gamma target walk →
      target = walk / eq8Factor E Gamma) := by
  exact eq8_unqualified_access_false

example (E Gamma target walk : ℝ) (hobs : eq8Observation E Gamma target walk)
    (hfactor : eq8Factor E Gamma ≠ 0) :
    target = walk / eq8Factor E Gamma := by
  exact eq8_recover_of_nonzero_factor E Gamma target walk hobs hfactor

end Tests.SpectralMeas17Counterexample
