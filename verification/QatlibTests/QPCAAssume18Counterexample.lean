module

import Qatlib.Papers.QPCAAssume18.QuantumCentroid.Counterexample

/-! Ordinary-module consumer test for the QPCAAssume18 normalization witness. -/

set_option autoImplicit false
noncomputable section

namespace QatlibTests.QPCAAssume18Counterexample

open Qatlib.Papers.QPCAAssume18.QuantumCentroid

/-- An ordinary consumer sees the explicit source refutation. -/
example :
    printedProjectionProbability (centroidLambda 1 (-1)) (centroidZ 1 (-1)) = 2 := by
  exact witness_printed_value

/-- An ordinary consumer sees the repaired normalized value. -/
example :
    correctedProjectionProbability (centroidLambda 1 (-1)) (centroidZ 1 (-1)) witnessMatrix = 1 := by
  exact witness_corrected_value

#print axioms witness_printed_value
#print axioms witness_corrected_value

end QatlibTests.QPCAAssume18Counterexample
