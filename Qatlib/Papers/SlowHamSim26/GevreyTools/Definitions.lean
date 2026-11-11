/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SlowHamSim26 / GevreyTools — shared Gevrey jet vocabulary

Fixed source: arXiv:2608.17653v1, *Quantum simulation of slow analytic
time-dependent Hamiltonians* (Zhao–Li–An).  This file records the paper's
Gevrey conventions (§2.2, Eq. (2.1)) and the two explicit cutoff constants of
Lemma 3.2, Eq. (3.7), so that every block of the paper can state its results
against the same objects.

`GevreyOn C D σ f` is the paper's condition
`‖f^(n)(t)‖ ≤ C · D^n · (n!)^σ` for every `n` and every `t`; for a matrix
valued `f` the norm is the spectral (L2 operator) norm of `Matrix`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SlowHamSim26.GevreyTools

open Real

/-- Fixed arXiv:2608.17653v1, Lemma 3.2 Eq. (3.7): `C_{τ,1} = e²/2`. -/
def Ctau1 (_τ : ℝ) : ℝ := Real.exp 2 / 2

/-- Fixed arXiv:2608.17653v1, Lemma 3.2 Eq. (3.7): `C_{τ,2} = 4e^{τ+1}/(τ-1)`. -/
def Ctau2 (τ : ℝ) : ℝ := 4 * Real.exp (τ + 1) / (τ - 1)

/-- Fixed arXiv:2608.17653v1, §2.2 Eq. (2.1): the Gevrey class `G^σ`
with explicit constants `C, D`.  `iteratedDeriv n f t` is the paper's
`f^{(n)}(t)`; for matrix-valued `f` the norm is the spectral norm. -/
def GevreyOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C D σ : ℝ) (f : ℝ → E) : Prop :=
  ∀ (n : ℕ) (t : ℝ), ‖iteratedDeriv n f t‖ ≤ C * D ^ n * (n.factorial : ℝ) ^ σ

/-- Fixed arXiv:2608.17653v1, §2.3: `2T`-periodicity for a time-dependent
Hamiltonian. -/
def PeriodicHamiltonian {d : ℕ} (H : ℝ → Matrix (Fin d) (Fin d) ℂ) (T : ℝ) : Prop :=
  ∀ t, H (t + 2 * T) = H t

end Qatlib.Papers.SlowHamSim26.GevreyTools
