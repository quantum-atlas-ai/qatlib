/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.Defs
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Papers.QLattice03.MainResults

noncomputable def svpExponent (f : ℝ) : ℝ := 1 / 2 + 2 * f

def SolvesDCPWithFailure (f : ℝ) (A : ∀ N : ℕ, DCPRegister N → ℤ) : Prop :=
  SolvesDCP A

def SolvesTwoPointWithFailure (f : ℝ)
    (A : ∀ n M : ℕ, TwoPointRegister n M → (Fin n → ℤ)) : Prop :=
  SolvesTwoPoint A

def HasDCPSolver (f : ℝ) : Prop := ∃ A, SolvesDCPWithFailure f A

def HasTwoPointSolver (f : ℝ) : Prop := ∃ A, SolvesTwoPointWithFailure f A

def ThetaUniqueSVP (e : ℝ)
    (B : ∀ n : ℕ, LatticeBasis n → (Fin n → ℤ)) : Prop :=
  ∃ c : ℝ, 0 < c ∧ SolvesUniqueSVP (fun n => c * (n : ℝ) ^ e) B

def PolyUniqueSVP (B : ∀ n : ℕ, LatticeBasis n → (Fin n → ℤ)) : Prop :=
  ∃ e : ℝ, 0 < e ∧ ThetaUniqueSVP e B

end Qatlib.Papers.QLattice03.MainResults
