module

public import Qatlib.Papers.NoisyCircuit22.MainResults.Paths.TwoQubitDepthOne

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace QatlibTests.NoisyCircuit22Regression

open Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel
open Qatlib.Papers.NoisyCircuit22.MainResults.Paths

/-- The ordinary module consumer invokes the concrete legal-path theorem. -/
example :
    legalPathCount 2 1 twoQubitDepthOneArchitecture 2 = 2 :=
  two_qubit_depth_one_legal_path_count

/-- The consumer also preserves the source-model boundary mismatch as an
explicit negative regression instead of importing an unproved count formula. -/
example :
    legalPathCount 2 1 twoQubitDepthOneArchitecture 2 ≠
      2 * 2 ^ 1 * 3 ^ (1 - 1) :=
  source_lemma6_formula_requires_fixed_terminal

end QatlibTests.NoisyCircuit22Regression
