module

public import Qatlib.Papers.ExactSimon97.MainResults.PolylogExact

@[expose] public section

/-!
# Concrete consumer for exact Section-6 progress

This ordinary-module consumer specializes the exact-amplification theorem to
four Euclidean coordinates and two marked labels. It assumes a preparation
with marked mass `1 / 2` and verifies the bound at exponent one.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace QatlibTests.ExactSimon97PolylogExactRegression

open Qatlib.Papers.ExactSimon97.MainResults.PolylogExact

/-- The first two labels form a marked half of the four-label consumer. -/
def markedHalf : Finset (Fin 4) := {0, 1}

/-- A concrete non-degenerate four-label instance of exact Section-6 progress:
the marked fraction is one half, and both registers are measured in the complex
Euclidean norm. -/
theorem four_label_exact_progress
    (A : EuclideanSpace ℂ (Fin 4) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 4))
    (hmass : ‖(exactSimonProjection 4 markedHalf)
        (A (coordinateBasis 4 ⟨0, by norm_num⟩))‖ ^ 2 =
      1 / ((2 : ℕ) : ℝ)) :
    ∃ (queryConstant : ℝ) (r : ℝ) (program : List (Fin 6)),
      0 < queryConstant ∧ 0 ≤ r ∧ r ≤ 1 ∧
      ‖(exactSimonRun (by norm_num) markedHalf A r program).1‖ ^ 2 +
        ‖(exactSimonRun (by norm_num) markedHalf A r program).2‖ ^ 2 = 1 ∧
      exactSimonGoodMass (by norm_num) markedHalf A r program = 1 ∧
      (Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls
        program : ℝ) ≤
        queryConstant * Real.logb 2 ((4 : ℕ) : ℝ) ^
          (((1 : ℕ) : ℝ) / 2) := by
  obtain ⟨queryConstant, hpositive, instanceLaw⟩ :=
    exactSimon_knownFraction_exact_program
  obtain ⟨r, program, hr0, hr1, hnorm, hgood, hcalls⟩ :=
    instanceLaw 4 2 1 ⟨0, by norm_num⟩ (by norm_num) (by norm_num)
      markedHalf A hmass
      (by
        have hlog : Real.logb 2 ((4 : ℕ) : ℝ) = 2 := by
          have h4 : ((4 : ℕ) : ℝ) = ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
          rw [h4, Real.logb_pow,
            Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
          norm_num
        rw [hlog]
        norm_num)
  exact ⟨queryConstant, r, program, hpositive, hr0, hr1, hnorm, hgood, hcalls⟩

end QatlibTests.ExactSimon97PolylogExactRegression
