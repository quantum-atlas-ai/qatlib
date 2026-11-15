/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

set_option autoImplicit false

set_option autoImplicit false

namespace Qatlib.Concepts.CodingDecoding.FamilyAssembly.FilteredKernels

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

noncomputable def meanOperator (h : ι → Matrix n n ℂ) : Matrix n n ℂ :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ i, h i

def copiedChecks {m r : ℕ} (h : Fin m → Matrix n n ℂ) :
    Fin r × Fin m → Matrix n n ℂ := fun p => h p.2

def copiedPaddedChecks {m r : ℕ} (h : Fin m → Matrix n n ℂ) (t : ℕ) :
    (Fin r × Fin m) ⊕ Fin t → Matrix n n ℂ :=
  Sum.elim (copiedChecks h) (fun _ => 0)

noncomputable def copyPaddingFactor (m r t : ℕ) : ℝ :=
  ((r * m : ℕ) : ℝ) / ((r * m + t : ℕ) : ℝ)

def traceEnergy (H ρ : Matrix n n ℂ) : ℝ := (Matrix.trace (H * ρ)).re

noncomputable def involutionCheck (S : Matrix n n ℂ) : Matrix n n ℂ :=
  (1 / 2 : ℝ) • (1 - S)

noncomputable def anticommutingPairGap : ℝ := 1 - Real.sqrt 2 / 2

noncomputable def anticommutingPairGram (S T : Matrix n n ℂ) : Matrix n n ℂ :=
  (Real.sqrt 2 : ℝ) • (1 : Matrix n n ℂ) - S - T

end Qatlib.Concepts.CodingDecoding.FamilyAssembly.FilteredKernels
