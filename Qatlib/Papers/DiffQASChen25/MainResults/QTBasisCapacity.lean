/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CircCompLiu24.MainResults.ParameterCompressionModel
public import Mathlib.Data.Fin.Embedding

@[expose] public section

/-!
# Computational-basis capacity in Quantum-Train

Section IV uses the ceiling binary logarithm of the parameter count as its register size.
The existing cardinality calculation gives an injection from parameter indices into that basis.
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.CircCompLiu24.MainResults

namespace Qatlib.Papers.DiffQASChen25.MainResults

/-- The Quantum-Train qubit count of §IV gives at least as many basis outcomes as parameters. -/
theorem qt_basis_capacity (p : ℕ) : p ≤ Fintype.card (Reg (qubitCount p)) :=
  card_reg_qubitCount_ge p

/-- The basis capacity permits distinct computational-basis labels for the parameter indices. -/
theorem qt_basis_encoding (p : ℕ) : Nonempty (Fin p ↪ Reg (qubitCount p)) :=
  ⟨(Fin.castLEEmb (qt_basis_capacity p)).trans
    (Fintype.equivFin (Reg (qubitCount p))).symm.toEmbedding⟩

end Qatlib.Papers.DiffQASChen25.MainResults
