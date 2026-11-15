/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GramQueryCore.QfiCompletion.MqfiRationalGramFactorizationStat
public import Qatlib.Foundations.MatrixAlgebra.GramFactor.RationalGramFactorization

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.GramQueryCore.QfiCompletion

open Qatlib.Foundations.MatrixAlgebra.GramFactor

/-- Establishes the rational Gram factorization property used in the MQFI construction. -/
theorem mqfiRationalGramFactorization : MqfiRationalGramFactorization := by
  intro n H hSym hPSD
  exact Qatlib.Foundations.MatrixAlgebra.GramFactor.exists_rational_gram_factorization n H hSym hPSD
end Qatlib.Concepts.GramQueryCore.QfiCompletion
