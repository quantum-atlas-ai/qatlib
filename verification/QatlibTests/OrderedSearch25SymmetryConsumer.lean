module

import Qatlib.Papers.OrderedSearch25.MainResults.SymmetryDeltaConjugation

/-!
# Output selector transport under a three-cycle

The cycle distinguishes forward reindexing from inverse reindexing. One
constant query bit supplies a nonempty query-location type.
-/

set_option autoImplicit false
set_option warningAsError true

namespace QatlibTests.OrderedSearch25SymmetryConsumer

open Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Qatlib.Papers.OrderedSearch25.MainResults
open scoped Matrix.Norms.L2Operator

/-- The permutation `0 → 1 → 2 → 0`. -/
private def cycle : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

/-- The same three-cycle on inputs and outputs preserves the constant query signs
and commutes with the identity output map. -/
private theorem cycle_symmetry :
    IsBssSymmetry (fun (_ : Fin 3) (_ : Fin 1) => false) id cycle 1 cycle := by
  constructor
  · intro i x x'
    simp [bssE]
  · intro x
    rfl

example (A : Matrix (Fin 3) (Fin 3) ℂ) :
    ((sourcePermMatrix cycle)⁻¹ * A * sourcePermMatrix cycle) 0 2 = A 1 0 :=
  sourcePermMatrix_conj_apply cycle A 0 2

example :
    bssDelta id (0 : Fin 3) =
      (sourcePermMatrix cycle)⁻¹ * bssDelta id 1 * sourcePermMatrix cycle := by
  exact source_proposition16_delta_conjugation (fun _ _ => false) id cycle 1 cycle
    cycle_symmetry 0

example : ‖sourcePermMatrix cycle‖ = 1 :=
  sourcePermMatrix_l2_opNorm_eq cycle

end QatlibTests.OrderedSearch25SymmetryConsumer
